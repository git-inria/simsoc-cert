(**
SimSoC-Cert, a library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Pseudocode abstract syntax tree.
*)

open Util;;

(*****************************************************************************)
(** expressions *)
(*****************************************************************************)

type mode = Fiq | Irq | Svc | Abt | Und | Usr | Sys;;

type size = Byte | Half | Word;;

let size_of_string = function
  | "4" -> Word
  | "2" -> Half
  | "1" -> Byte
  | _ -> invalid_arg "Ast.size_of_string";;

type exp =
| Num of string
| Bin of string
| Hex of string
| If_exp of exp * exp * exp
| Fun of string * exp list
| BinOp of exp * string * exp
| CPSR
| SPSR of mode option
| Reg of exp * mode option
| Var of string
| Range of exp * range
| Unaffected
| Unpredictable_exp
| Memory of exp * size
| Coproc_exp of exp * string * exp list

and range =
| Bits of string * string
| Flag of string * string (* 2nd arg is the name used like "Flag" or "bit" *)
| Index of exp;;

(* arguments of a BinOp after flattening *)
let args = function
  | BinOp (_, f, _) as e ->
      let rec aux = function
	| BinOp (e1, g, e2) when g = f -> aux e1 @ aux e2
	| e -> [e]
      in aux e
  | e -> [e];;

(*****************************************************************************)
(** instructions *)
(*****************************************************************************)

type inst =
| Block of inst list
| Unpredictable
| Affect of exp * exp
| If of exp * inst * inst option
| Proc of string * exp list
| While of exp * inst
| Assert of exp
| For of string * string * string * inst
| Coproc of exp * string * exp list
| Case of exp * (string * inst) list;;

(*****************************************************************************)
(** program names *)
(*****************************************************************************)

type ident = {
  iname : string;
  iparams : string list;
  ivariant : string option };;

(* convert a list of strings into an underscore-separated string *)
let rec underscore = function
  | [] -> ""
  | [s] -> s
  | s :: ss -> s ^ "_" ^ underscore ss;;

(* convert a list of strings into an ident *)
let ident ss = { iname = underscore ss; iparams = []; ivariant = None };;

(*****************************************************************************)
(** programs *)
(*****************************************************************************)

type kind =
  | Inst (* instruction *)
  | Mode of int (* addressing mode *);;

type prog = {
  pref : string; (* chapter in the ARM documentation (e.g. A4.1.20) *)
  pkind : kind;
  pident : ident;
  pidents : ident list; (* alternative idents *)
  pinst : inst };;

(*****************************************************************************)
(** addressing modes *)
(*****************************************************************************)

(* heuristic providing the addressing mode from a list of strings *)
let addr_mode ss =
  match ss with
    | "Data" :: _ -> 1
    | "Miscellaneous" :: _ -> 3
    | _ :: _ :: _ :: s :: _ ->
	begin match s with
	  | "Word" -> 2
	  | "Multiple" -> 4
	  | "Coprocessor" -> 5
	  | _ -> invalid_arg "Ast.add_mode"
	end
    | _ -> invalid_arg "Ast.addr_mode";;

(* heuristic providing the addressing mode of a program from its name
   and its list of global variables *)
let addr_mode_of_prog =
  let mode3 = set_of_list ["LDRD";"LDRH";"LDRSB";"LDRSH";"STRD";"STRH"] in
  let mode4 = set_of_list ["RFE";"SRS"] in
  let mode5 = set_of_list ["LDC";"STC"] in
    fun p (gs : (string * string) list) ->
      if List.mem_assoc "shifter_operand" gs then Some 1
      else if List.mem_assoc "address" gs then
	if StrSet.mem p.pident.iname mode3 then Some 3 else Some 2
      else if List.mem_assoc "register_list" gs
	|| StrSet.mem p.pident.iname mode4 then Some 4
      else if StrSet.mem p.pident.iname mode5 then Some 5
      else None;;

(* provides the variables computed by an addressing mode *)
let mode_vars = function
  | 1 -> ["shifter_operand"; "shifter_carry_out"]
  | 2 | 3 -> ["address"]
  | 4 | 5 -> ["start_address"; "end_address"]
  | _ -> invalid_arg " Ast.mode_vars";;

(* set of variables computed by addressing modes *) 
let mode_variables =
  let s = ref StrSet.empty in
    for i = 1 to 5 do
      s := StrSet.union !s (set_of_list (mode_vars i))
    done; !s;;

let is_mode_var s =  StrSet.mem s mode_variables;;

let remove_mode_vars gs = List.filter (fun (s, _) -> not (is_mode_var s)) gs;;

(*****************************************************************************)
(** global, local and mode variables of a program *)
(*****************************************************************************)

module type Var = sig
  type typ;;
  val global_type : string -> typ;;
  val local_type : string -> exp -> typ;;
  val key_type : typ;;
end;;

let output_registers = set_of_list ["d"; "dHi"; "dLo"; "n"];;

module Make (G : Var) = struct

  (* add every variable as global except if it is already declared as
     local or if its the for-loop variable "i" *)
  let rec vars_exp ((gs,ls) as acc) = function
    | Var s  ->
	if StrMap.mem s ls || s = "i" (* variable used in for-loops *)
	then acc
	else StrMap.add s (G.global_type s) gs, ls
    | If_exp (e1, e2, e3) -> vars_exp (vars_exp (vars_exp acc e1) e2) e3
    | Fun (_, es) -> vars_exps acc es
    | Range (e1, Index e2) | BinOp (e1, _, e2) -> vars_exp (vars_exp acc e1) e2
    | Range (e, _) | Reg (e, _) | Memory (e, _) -> vars_exp acc e
    | Coproc_exp (e, _ , es) -> vars_exps (vars_exp acc e) es
    | _ -> acc

  and vars_exps acc es = List.fold_left vars_exp acc es;;

  (* add every affected variable as local except if it is an output
     register *)
  let rec vars_inst ((gs,ls) as acc) = function
    | Affect (Var s, e) | Affect (Range (Var s, _), e) -> vars_exp
	(if StrSet.mem s output_registers
	 then StrMap.add s (G.global_type s) gs, ls
	 else gs, StrMap.add s (G.local_type s e) ls) e
    | Affect (e1, e2) -> vars_exp (vars_exp acc e1) e2
    | Block is -> vars_insts acc is
    | If (e, i, None) | While (e, i) -> vars_inst (vars_exp acc e) i
    | If (e, i1, Some i2) -> vars_inst (vars_inst (vars_exp acc e) i1) i2
    | Proc (_, es) -> vars_exps acc es
    | For (_, _, _, i) -> vars_inst acc i
    | Coproc(e, _ , es) -> vars_exps (vars_exp acc e) es
    | Case (e, nis) -> vars_cases (vars_exp acc e) nis
    | _ -> acc

  and vars_insts acc is = List.fold_left vars_inst acc is

  and vars_cases acc nis =
    List.fold_left (fun acc (_, i) -> vars_inst acc i) acc nis;;

  let vars p =
    let gs, ls = vars_inst (StrMap.empty, StrMap.empty) p.pinst in
      list_of_map gs, list_of_map ls;;

end;;
