(**
SimSoC-Cert, a library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Pseudocode abstract syntax tree.
*)

type mode = Fiq | Irq | Svc | Abt | Und | Usr | Sys;;

type num = string;;

type size = Byte | Half | Word;;

let size_of_num = function
  | "4" -> Word
  | "2" -> Half
  | "1" -> Byte
  | _ -> invalid_arg "Ast.size_of_num";;

type exp =
| Num of num
| Bin of num
| Hex of num
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
| Bits of num * num
| Flag of string * string (* 2nd arg is the name used like "Flag" or "bit" *)
| Index of exp;;

let args = function
  | BinOp (_, f, _) as e ->
      let rec aux = function
	| BinOp (e1, g, e2) when g = f -> aux e1 @ aux e2
	| e -> [e]
      in aux e
  | e -> [e];;

type inst =
| Block of inst list
| Unpredictable
| Affect of exp * exp
| If of exp * inst * inst option
| Proc of string * exp list
| While of exp * inst
| Assert of exp
| For of string * num * num * inst
| Coproc of exp * string * exp list
| Case of exp * (num * inst) list;;

type ident = { iname : string; iparams : string list; ivariant : num option };;

type addr_mode = Data | LoadWord | LoadMisc | LoadMul | LoadCoproc;;

type kind = Inst | Mode of addr_mode;;

type prog = {
  pref : string;
  pkind : kind;
  pident : ident;
  pidents : ident list;
  pinst : inst };;

let addr_mode ss =
  match ss with
    | "Data" :: _ -> Data
    | "Miscellaneous" :: _ -> LoadMisc
    | _ :: _ :: _ :: s :: _ ->
	begin match s with
	  | "Word" -> LoadWord
	  | "Multiple" -> LoadMul
	  | "Coprocessor" -> LoadCoproc
	  | _ -> invalid_arg "Ast.add_mode"
	end
    | _ -> invalid_arg "Ast.add_mode";;

let rec name = function
  | [] -> ""
  | s :: ss -> s ^ "_" ^ name ss;;

let ident ss = { iname = name ss; iparams = []; ivariant = None };;
