(**
SimSoC-Cert, a library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Pseudocode syntax and semantics.
*)


(****************************************************************************)
(** Pseudo-code expressions *)
(****************************************************************************)

type nat = int;; (*IMPROVE: use a private data type?*)

type word = int;;

type processor_exception_mode = Fiq | Irq | Svc | Abt | Und;;

type range = All | Bit of nat | Bits of nat * nat;;

type exp =
| Var of nat
| Word of word
| State of sexp * range
| If of bexp * exp * exp
| Add of exp * exp
| CarryFrom_add2 of exp * exp
| OverflowFrom_add2 of exp * exp
| CarryFrom_add3 of exp * exp * exp
| OverflowFrom_add3 of exp * exp * exp

and sexp =
| CPSR
| SPSR of processor_exception_mode
| Reg of exp
| Reg_exn of processor_exception_mode * exp

and bexp =
| Eq of exp * exp
| ConditionPassed
| BAnd of bexp * bexp;;

(****************************************************************************)
(** Pseudo-code instructions *)
(****************************************************************************)

type inst =
| Unpredictable
| Seq of inst * inst
| Affect of sexp * range * exp
| IfThen of bexp * inst
| IfThenElse of bexp * inst * inst
| Affect_CPSR_SPSR;;
