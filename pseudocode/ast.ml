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

(* processor modes *)
type mode = Fiq | Irq | Svc | Abt | Und | Usr | Sys;;

(* word sizes read from/written to memory *)
type size = Byte | Half | Word;;

(* convert a number string into a word size *)
let size_of_string = function
  | "4" -> Word
  | "2" -> Half
  | "1" -> Byte
  | _ -> invalid_arg "Ast.size_of_string";;

type exp =
| Num of string
| Bin of string
| Hex of string
| Float_zero
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

type type_param = 
    Tint | Tlong | Tfloat | Tdouble | Tvoid | Tunsigned_long | Tunsigned_char | Tunsigned_short | Tchar | Tbool

type inst =
| Block of inst list
| Let of (type_param * string) * (type_param * string) list * inst list * inst
| Unpredictable
| Affect of exp * exp
| If of exp * inst * inst option
| Proc of string * exp list
| While of exp * inst
| Assert of exp
| For of string * string * string * inst
| Coproc of exp * string * exp list
| Case of exp * (string * inst) list * inst option
| Return of exp;;

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
  | InstARM (* instruction on 32 bits *)
  | InstThumb (* instruction on 16 bits *)
  | Mode of int (* addressing mode *);;

type prog = {
  pref : string; (* chapter in the ARM documentation (e.g. A4.1.20) *)
  pkind : kind;
  pident : ident;
  pidents : ident list; (* alternative idents *)
  pinst : inst };;

type program = {
  header : inst list; (* for ARM, this list is always nil *)
  body : prog list }

(* s should be the reference of the program *)
let is_thumb s = s.[1] = '7';;

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
  let no_mode = set_of_list ["SWP"; "SWPB"] in
    fun p (gs : (string * string) list) ->
      if List.mem_assoc "shifter_operand" gs then Some 1
      else if List.mem_assoc "address" gs then
        if StrSet.mem p.pident.iname no_mode then None
	else if StrSet.mem p.pident.iname mode3 then Some 3 else Some 2
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
(** Global and local variables of a program and their types in
    the target language. A variable is:
- global if it is not local,
- local if it is affected to some value.
The variable "i" used in for-loops is not counted in variables. *)
(*****************************************************************************)

module type Var = sig
  (* type of target language types *)
  type typ
  (* type of a variable from its name *)
  val global_type : string -> typ
  (* type of a local variable from its name and the expression to
     which it is affected *)
  val local_type : string -> exp -> typ
  (* type of variables used in case instructions *)
  val explicit_annot_type : type_param -> typ
  (* internal representation of [type_param], they are equivalent *)
  val case_type : typ
end;;

(* register variables that are set by instructions *)
let output_registers = set_of_list ["d"; "dHi"; "dLo"; "n"];;

module Make (G : Var) = struct

  (* add every variable as global except if it is already declared as
     local. Note that the for-loop variable is added, but will be removed in
     [vars_inst]. *)
  let rec vars_exp ((gs,ls) as acc) = function
    | Var s when not (StrMap.mem s ls) ->
	(StrMap.add_no_erase s (G.global_type s) gs), ls
    | If_exp (e1, e2, e3) -> vars_exp (vars_exp (vars_exp acc e1) e2) e3
    | Fun (_, es) -> vars_exps acc es
    | Range (e1, Index e2) | BinOp (e1, _, e2) -> vars_exp (vars_exp acc e1) e2
    | Range (e, _) | Reg (e, _) | Memory (e, _) -> vars_exp acc e
    | Coproc_exp (e, _ , es) -> vars_exps (vars_exp acc e) es
    | _ -> acc

  and vars_exps acc es = List.fold_left vars_exp acc es;;

  (* add every affected variable as local except if it is an output
     register or in a case instruction *)
  let rec vars_inst ((gs,ls) as acc) = function
    | Affect (Var s, e) | Affect (Range (Var s, _), e) -> vars_exp
	(if StrSet.mem s output_registers
	 then StrMap.add_no_erase s (G.global_type s) gs, ls
	 else gs, StrMap.add_no_erase s (G.local_type s e) ls) e
    | Affect (e1, e2) -> vars_exp (vars_exp acc e1) e2
    | Block is -> vars_insts acc is
    | Let (_, ns, is, i) -> vars_inst (vars_insts (List.fold_left (fun gs (ty, n) -> 
      StrMap.add n (G.explicit_annot_type ty) gs) gs ns, ls) is) i
    | If (e, i, None) | While (e, i) -> vars_inst (vars_exp acc e) i
    | If (e, i1, Some i2) -> vars_inst (vars_inst (vars_exp acc e) i1) i2
    | Proc (_, es) -> vars_exps acc es
    | For (v, _, _, i) -> let gs, ls = vars_inst acc i in StrMap.remove v gs, ls
    | Coproc(e, _ , es) -> vars_exps (vars_exp acc e) es
    | Case (Var s, nis, o) -> 
      let gs', ls = 
	vars_cases (StrMap.add s G.case_type gs, ls) 
	  (let nis = List.map snd nis in
	   match o with None -> nis | Some ni -> nis @ [ni]) in
      ((* Now, we can just return [gs'], but the functions [G.case_type] and [G.global_type _] 
	  do not necessarily return the same type description. So by default, we choose to restore 
	  the initial value associated to [s] in [gs]. *)
	if StrMap.mem s gs then
	  StrMap.add s (let v0 = StrMap.find s gs in 
			let () = 
			  if v0 = StrMap.find s gs' then
			    ()
			  else 
			    Printf.eprintf "warning: inside the Case, '%s' has a \
                            different type than it has outside\n%!" s in 
			v0) gs'
       else
	  gs'), ls
    | _ -> acc

  and vars_insts acc is = List.fold_left vars_inst acc is

  and vars_cases acc nis = List.fold_left vars_inst acc nis;;

  (* sort variables by their names *)
  let vars (i: inst) =
    let gs, ls = vars_inst (StrMap.empty, StrMap.empty) i in
      list_of_map gs, list_of_map ls;;

end;;

(*****************************************************************************)
(** Manipulations of ASTs *)
(*****************************************************************************)

(* replace each expression using f (innermost first) *)
let ast_map (fi: inst -> inst) (fe: exp -> exp) (i: inst) =
  let rec exp e =
    let e' = match e with
      | If_exp (e1, e2, e3) -> If_exp (exp e1, exp e2, exp e3)
      | Fun (s, es) -> Fun (s, List.map exp es)
      | BinOp (e1, s, e2) -> BinOp (exp e1, s, exp e2)
      | Reg (e, m) -> Reg (exp e, m)
      | Range (e, r) -> Range (exp e, range r)
      | Memory (e, s) -> Memory (exp e, s)
      | Coproc_exp (e, s, es) -> Coproc_exp (exp e, s, List.map exp es)
      | x -> x
    in fe e'
  and range r = match r with
    | Index e -> Index (exp e)
    | x -> x
  and inst i =
    let i' = match i with
    | Block is -> Block (List.map inst is)
    | Affect (e1, e2) -> Affect (exp e1, exp e2)
    | If (e, i1, Some i2) -> If (exp e, inst i1, Some (inst i2))
    | If (e, i, None) -> If (exp e, inst i, None)
    | Proc (s, es) -> Proc (s, List.map exp es)
    | While (e, i) -> While (exp e, inst i)
    | Assert e -> Assert (exp e)
    | For (s1, s2, s3, i) -> For (s1, s2, s3, inst i)
    | Coproc (e, s, es) -> Coproc (exp e, s, List.map exp es)
    | Case (e, sis, oi) ->
        Case (exp e, List.map (fun (s, i) -> (s, inst i)) sis, 
	      option_map inst oi)
    | x -> x
    in fi i'
  in inst i;;

(* replace expression 'o' by expresssion 'n' in instruction 'i' *)
let replace_exp (o: exp) (n: exp) (i: inst) =
  let exp e = if e = o then n else e in
  let i' = ast_map (fun x -> x) exp i in
    if i = i' then raise Not_found else i';;

(* replace instruction 'o' by instruction 'n' in instruction 'i' *)
let replace_inst (o: inst) (n: inst) (i: inst) =
  let inst e = if e = o then n else e in
  let i' = ast_map inst (fun x -> x) i in
    if i = i' then raise Not_found else i';;

(* Check whether a sub-tree of the expression e satisifies pe (expression
 * predicate) of pr (range predicate) *)
let rec exp_exists pe pr =
  let rec exp e = if pe e then true else match e with
   | If_exp (e1, e2, e3) -> exp e1 || exp e2 || exp e3
   | Fun (_, es) -> List.exists exp es
   | BinOp (e1, _, e2) -> exp e1 || exp e2
   | Reg (e, _) -> exp e
   | Range (e, r) -> exp e || range_exists pe pr r
   | Memory (e, _) -> exp e 
   | Coproc_exp (e, _, es) -> exp e || List.exists exp es
   | _ -> false
  in exp
(* same for ranges *)
and range_exists pe pr r = if pr r then true else match r with
  | Index e -> exp_exists pe pr e
  | _ -> false;;

(* same for instructions *)
let inst_exists pi pe pr =
  let exp = exp_exists pe pr in
  let rec inst i = if pi i then true else match i with
    | Block is -> List.exists inst is
    | Let (_, _, is, i) -> List.exists inst is || inst i
    | Unpredictable -> false
    | Affect (e1, e2) -> exp e1 || exp e2
    | If (e, i, None) -> exp e || inst i
    | If (e, i1, Some i2) -> exp e || inst i1 || inst i2
    | Proc (_, es) -> List.exists exp es
    | While (e, i) -> exp e || inst i
    | Assert e -> exp e
    | For (_, _, _, i) -> inst i
    | Coproc (e, _, es) -> exp e || List.exists exp es
    | Case (e, sis, oi) -> exp e || List.exists (fun (_,i) -> inst i) sis ||
      option_exists inst oi
    | Return e -> exp e
  in inst;;

let ftrue _ = true and ffalse _ = false;;
