(**
SimSoC-Cert, a library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Pseudocode abstract syntax tree.
*)

(****************************************************************************)
(** Pseudo-code expressions *)
(****************************************************************************)

type num = int;; (*IMPROVE: use a private data type?*)

type word = int;; (*FIXME: use int32?*)

let word_of_num n = n;;

type processor_exception_mode = Fiq | Irq | Svc | Abt | Und;;

type flag = N | Z | C | V;;

type range = Bit of num | Bits of num * num;;

type exp =
| Word of word
| State of sexp
| If of exp * exp * exp
| Fun of string * exp list
| Range of exp * range
| Other of string list

and sexp =
| CPSR
| SPSR of processor_exception_mode
| Reg of processor_exception_mode option * num
| Var of string
| Flag of flag;;

(****************************************************************************)
(** Pseudo-code instructions *)
(****************************************************************************)

type inst =
| Block of inst list
| Unpredictable
| Affect of sexp * range option * exp
| IfThenElse of exp * inst * inst option;;

type prog = string * string * inst;;
