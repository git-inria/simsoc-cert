(**
SimSoC-Cert, a Coq library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Chapter A4 - ARM Instructions (p. 150)
*)

Set Implicit Arguments.

Require Import Shift.
Require Import Bitvec.
Require Import State.

Inductive instruction : Type :=
| ADC (S : bool) (Rd Rn : reg_num) (so : shifter_operand)
| ADD (S : bool) (Rd Rn : reg_num) (so : shifter_operand)
| AND (S : bool) (Rd Rn : reg_num) (so : shifter_operand)
| BL (L : bool) (w : word).
