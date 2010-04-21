(**
SimSoC-Cert, a Coq library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Chapter A4 - ARM Instructions (p. 150)
*)

Set Implicit Arguments.

Require Import Bitvec.
Require Import State.

(****************************************************************************)
(* Chapter A4 - ARM Instructions (p. 151) *)
(****************************************************************************)
(* S : S bit (bit[20]) *)
(* d : Specifieds the destination register Rd *)
(* n : Specifies the first source operand register Rn *)
(* L : L bit (bit[24]) *)
(* w : target address *)
Inductive instruction : Type :=
| ADC (cond : opcode) (S : bool) (d n : reg_num) (so : shifter_operand)
| ADD (cond : opcode) (S : bool) (d n : reg_num) (so : shifter_operand)
| AND (cond : opcode) (S : bool) (d n : reg_num) (so : shifter_operand)
| BL (cond : opcode) (L : bool) (w : word).
