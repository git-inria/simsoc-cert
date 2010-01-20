(**
SimSoC-Cert, a library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Pseudocode abstract syntax tree.
*)

type processor_exception_mode = Fiq | Irq | Svc | Abt | Und | Usr | Sys;;

type num = string;;

type exp =
| Num of num
| Bin of string
| Hex of string
| If_exp of exp * exp * exp
| Fun of string * exp list
| BinOp of exp * string * exp
| Other of string list
| CPSR
| SPSR of processor_exception_mode option
| Reg of exp * processor_exception_mode option
| Var of string
| Range of exp * range
| Unaffected
| Unpredictable_exp
| Memory of exp * num
| Coproc_exp of exp * string * exp list

and range =
| Bits of num * num
| Flag of string * string (* 2nd arg is the name used like "Flag" or "bit" *)
| Index of exp;;

type inst =
| Block of inst list
| Unpredictable
| Affect of exp * exp
| If of exp * inst * inst option
| Proc of string * exp list
| While of exp * inst
| Assert of exp
| For of string * num * num * inst
| Misc of string list
| Coproc of exp * string * exp list;;

type ident = {
  iname : string;
  ivars : string list;
  iversion : num option };;

type prog = {
  pref : string;
  pident : ident;
  paltidents : ident list;
  pinst : inst };;

let args = function
  | BinOp (_, f, _) as e ->
      let rec aux = function
	| BinOp (e1, g, e2) when g = f -> aux e1 @ aux e2
	| e -> [e]
      in aux e
  | e -> [e];;
