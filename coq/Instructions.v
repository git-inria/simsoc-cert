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
(* A3.2 The condition field (p. 111) *)
(****************************************************************************)

Inductive opcode : Type :=
| EQ | NE | CS | CC | MI | PL | VS | VC
| HI | LS | GE | LT | GT | LE | AL | UN.

Notation HS := CS.
Notation LO := CC.

(****************************************************************************)
(** A5.1 Addressing Mode 1 - Data-processing operands (p. 442)*)
(****************************************************************************)

Inductive shifter : Type := LSL | LSR | ASR | ROR.

Inductive shifter_value : Type :=
| ValImm (shift_imm : word) (*Immediate operand value*)
| ValReg (Rs : reg_num) (*Register operand value*).

(* Imm : Immediate
   Shift : Immediate shift/Register shift
   RRX : Register/Rotate right with extend. *)
Inductive shifter_operand : Type :=
| Imm (rotate_imm immed_8 : word)
| Shift (Rm : reg_num) (s : shifter) (v : shifter_value)
| RRX (Rm : reg_num).

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
