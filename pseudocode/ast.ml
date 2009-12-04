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

type range = All | Bit of num | Bits of num * num;;

type exp =
| Word of word
| State of sexp * range
| If of exp * exp * exp
| Fun of string * exp list
| Var of string

and sexp =
| CPSR
| SPSR of processor_exception_mode
| Reg of processor_exception_mode option * exp;;

(****************************************************************************)
(** Pseudo-code instructions *)
(****************************************************************************)

type inst =
| Unpredictable
| Seq of inst * inst
| Affect of sexp * range * exp
| IfThenElse of exp * inst * inst option;;
