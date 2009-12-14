(**
SimSoC-Cert, a library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Pseudocode abstract syntax tree.
*)

type processor_exception_mode = Fiq | Irq | Svc | Abt | Und;;

type num = string;;

type exp =
| Num of num
| Bin of string
| Hex of string
| If of exp * exp * exp
| Fun of string * exp list
| BinOp of exp * string * exp
| Other of string list
| CPSR
| SPSR of processor_exception_mode option
| Reg of (num * processor_exception_mode option)
| Var of string
| RdPlus1
| Range of exp * range
| Unaffected
| UnpredictableValue

and range =
| Bits of num * num
| Flag of string * string
| Index of exp list;;

type inst =
| Block of inst list
| Unpredictable
| Affect of exp * exp
| IfThenElse of exp * inst * inst option
| Proc of string * exp list
| While of exp * inst
| Assert of exp
| For of string * num * num * inst
| Misc of string list;;

type prog = {
  pref : string;
  pname : string;
  paltnames : string list;
  pvars : string list;
  pversion : num option;
  pinst : inst };;
