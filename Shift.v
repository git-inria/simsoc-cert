(**
SimSoC-Cert, a Coq library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

A5.1 Addressing Mode 1 - Data-processing operands (p. 442)
*)

Set Implicit Arguments.

Require Import Bitvec.
Require Import Coqlib.
Require Import State.
Require Import PseudoCode.
Require Import Integers. Import Int.
Require Import Util.

(****************************************************************************)
(* Type for shifter operands *)
(****************************************************************************)

Inductive shifter : Type := LSL | LSR | ASR | ROR.

Inductive shifter_value : Type :=
| ValImm (shift_imm : word)
| ValReg (Rs : reg_num).

Inductive shifter_operand : Type :=
| Imm (rotate_imm immed_8 : word)
| Shift (Rm : reg_num) (s : shifter) (v : shifter_value)
| RRX (Rm : reg_num).

(****************************************************************************)
(* A5.1.1 Encoding (p. 443) *)
(****************************************************************************)

Definition decode_shifter (w : word) : shifter :=
  match bits_val 5 6 w with
    | (*00*) 0 => LSL
    | (*01*) 1 => LSR
    | (*10*) 2 => ASR
    | (*11*) _ => ROR
  end.

Definition decode_shifter_operand (w : word) (x z : bool) : shifter_operand :=
  if x then Imm (bits 8 11 w) (bits 0 7 w)
  else Shift (reg_num_of 0 w) (decode_shifter w)
    (if z then ValImm (bits 7 11 w) else ValReg (reg_num_of 8 w)).

(*FIXME: duplicate the following functions in case you do not need to
compute the carry *)

(****************************************************************************)
(* A5.1.3 Data-processing operands - Immediate (p. 446) *)
(****************************************************************************)

(*
shifter_operand = immed_8 Rotate_Right (rotate_imm * 2)
if rotate_imm == 0 then
  shifter_carry_out = C flag
else /* rotate_imm != 0 */
  shifter_carry_out = shifter_operand[31]
*)

Definition so_imm (i : word) (rotate_imm immed_8 : word) : word * bool :=
  let v := Rotate_Right immed_8 (mul w2 rotate_imm) in
  let c := if zeq rotate_imm 0 then is_set Cbit i else is_set 31 v in
  (v, c).

(****************************************************************************)
(* A5.1.4 Data-processing operands - Register (p. 448) *)
(****************************************************************************)

(*
shifter_operand = Rm
shifter_carry_out = C Flag
*)

Definition so_reg (s : state) (m : processor_mode) (i : word) (Rm : reg_num)
  : word * bool := (reg_content s m Rm, is_set Cbit i).

(****************************************************************************)
(* A5.1.5 Data-processing operands - Logical shift left by immediate
   (p. 449) *)
(****************************************************************************)

(*
if shift_imm == 0 then /* Register Operand */
shifter_operand = Rm
shifter_carry_out = C Flag
else /* shift_imm > 0 */
shifter_operand = Rm Logical_Shift_Left shift_imm
shifter_carry_out = Rm[32 - shift_imm]
*)

Definition so_LSL_imm (s : state) (m : processor_mode) (i : word)
  (Rm : reg_num) (shift_imm : word) : word * bool :=
  let Rm := reg_content s m Rm in
  if zeq shift_imm 0 then (Rm, is_set Cbit i)
  else (Logical_Shift_Left Rm shift_imm,
    is_set (nat_of_Z (32 - shift_imm)) Rm).

(****************************************************************************)
(* A5.1.6 Data-processing operands - Logical shift left by register
   (p. 450) *)
(****************************************************************************)

(*
if Rs[7:0] == 0 then
  shifter_operand = Rm
  shifter_carry_out = C Flag
else if Rs[7:0] < 32 then
  shifter_operand = Rm Logical_Shift_Left Rs[7:0]
  shifter_carry_out = Rm[32 - Rs[7:0]]
else if Rs[7:0] == 32 then
  shifter_operand = 0
  shifter_carry_out = Rm[0]
else /* Rs[7:0] > 32 */
  shifter_operand = 0
  shifter_carry_out = 0
*)

Definition so_LSL_reg (s : state) (m : processor_mode) (i : word)
  (Rm Rs : reg_num) : word * bool :=
  let Rm := reg_content s m Rm in
  let Rs7 := bits 0 7 (reg_content s m Rs) in
  if zeq Rs7 0 then (Rm, is_set Cbit i)
  else match Zcompare Rs7 32 with
         | Lt => (Logical_Shift_Left Rm Rs7, is_set (nat_of_Z (32 - Rs7)) Rm)
         | Eq => (w0, is_set 0 Rm)
         | Gt => (w0, false)
       end.

(****************************************************************************)
(* A5.1.7 Data-processing operands - Logical shift right by immediate
   (p. 451) *)
(****************************************************************************)

(*
if shift_imm == 0 then
  shifter_operand = 0
  shifter_carry_out = Rm[31]
else /* shift_imm > 0 */
  shifter_operand = Rm Logical_Shift_Right shift_imm
  shifter_carry_out = Rm[shift_imm - 1]
*)

Definition so_LSR_imm (s : state) (m : processor_mode) (i : word)
  (Rm : reg_num) (shift_imm : word) : word * bool :=
  let Rm := reg_content s m Rm in
  if zeq shift_imm 0 then (w0, is_set 31 Rm)
  else (Logical_Shift_Right Rm shift_imm,
    is_set (pred (nat_of_Z shift_imm)) Rm).

(****************************************************************************)
(* A5.1.8 Data-processing operands - Logical shift right by register
   (p. 452) *)
(****************************************************************************)

(*
if Rs[7:0] == 0 then
  shifter_operand = Rm
  shifter_carry_out = C Flag
else if Rs[7:0] < 32 then
  shifter_operand = Rm Logical_Shift_Right Rs[7:0]
  shifter_carry_out = Rm[Rs[7:0] - 1]
else if Rs[7:0] == 32 then
  shifter_operand = 0
  shifter_carry_out = Rm[31]
else /* Rs[7:0] > 32 */
  shifter_operand = 0
  shifter_carry_out = 0
*)

Definition so_LSR_reg (s : state) (m : processor_mode) (i : word)
  (Rm Rs : reg_num) : word * bool :=
  let Rm := reg_content s m Rm in
  let Rs7 := bits 0 7 (reg_content s m Rs) in
  if zeq Rs7 0 then (Rm, is_set Cbit i)
  else match Zcompare Rs7 32 with
         | Lt => (Logical_Shift_Right Rm Rs7, is_set (pred (nat_of_Z Rs7)) Rm)
         | Eq => (w0, is_set 31 Rm)
         | Gt => (w0, false)
       end.

(****************************************************************************)
(* A5.1.9 Data-processing operands - Arithmetic shift right by immediate
   (p. 453) *)
(****************************************************************************)

(*
if shift_imm == 0 then
  if Rm[31] == 0 then
    shifter_operand = 0
    shifter_carry_out = Rm[31]
  else /* Rm[31] == 1 */
    shifter_operand = 0xFFFFFFFF
    shifter_carry_out = Rm[31]
else /* shift_imm > 0 */
  shifter_operand = Rm Arithmetic_Shift_Right <shift_imm>
  shifter_carry_out = Rm[shift_imm - 1]
*)

Definition so_ASR_imm (s : state) (m : processor_mode) (i : word)
  (Rm : reg_num) (shift_imm : word) : word * bool :=
  let Rm := reg_content s m Rm in
  if zeq shift_imm 0 then
    if is_set 31 Rm then (maxu, true) else (w0, false)
  else (Arithmetic_Shift_Right Rm shift_imm,
    is_set (pred (nat_of_Z shift_imm)) Rm).

(****************************************************************************)
(* A5.1.10 Data-processing operands - Arithmetic shift right by register
   (p. 454) *)
(****************************************************************************)

(*
if Rs[7:0] == 0 then
  shifter_operand = Rm
  shifter_carry_out = C Flag
else if Rs[7:0] < 32 then
  shifter_operand = Rm Arithmetic_Shift_Right Rs[7:0]
  shifter_carry_out = Rm[Rs[7:0] - 1]
else /* Rs[7:0] >= 32 */
  if Rm[31] == 0 then
    shifter_operand = 0
    shifter_carry_out = Rm[31]
  else /* Rm[31] == 1 */
    shifter_operand = 0xFFFFFFFF
    shifter_carry_out = Rm[31]
*)

Definition so_ASR_reg (s : state) (m : processor_mode) (i : word)
  (Rm Rs : reg_num) : word * bool :=
  let Rm := reg_content s m Rm in
  let Rs7 := bits 0 7 (reg_content s m Rs) in
  if zeq Rs7 0 then (Rm, is_set Cbit i)
  else match Zcompare Rs7 32 with
         | Lt => (Arithmetic_Shift_Right Rm Rs7,
           is_set (pred (nat_of_Z Rs7)) Rm)
         | _ => if is_set 31 Rm then (maxu, true) else (w0, false)
       end.

(****************************************************************************)
(* A5.1.11 Data-processing operands - Rotate right by immediate (p. 455) *)
(****************************************************************************)

(*
if shift_imm == 0 then
  See "Data-processing operands - Rotate right with extend" on page A5-17
  (p. 457)
else /* shift_imm > 0 */
  shifter_operand = Rm Rotate_Right shift_imm
  shifter_carry_out = Rm[shift_imm - 1]
*)

Definition so_ROR_imm (s : state) (m : processor_mode) (i : word)
  (Rm : reg_num) (shift_imm : word) : word * bool :=
  let Rm := reg_content s m Rm in
  if zeq shift_imm 0 then
    (or (Logical_Shift_Left (get Cbit i) w31) (Logical_Shift_Right Rm w1),
      is_set 0 Rm)
  else (Rotate_Right Rm shift_imm, is_set (pred (nat_of_Z shift_imm)) Rm).

(****************************************************************************)
(* A5.1.12 Data-processing operands - Rotate right by register (p. 456) *)
(****************************************************************************)

(*
if Rs[7:0] == 0 then
  shifter_operand = Rm
  shifter_carry_out = C Flag
else if Rs[4:0] == 0 then
  shifter_operand = Rm
  shifter_carry_out = Rm[31]
else /* Rs[4:0] > 0 */
  shifter_operand = Rm Rotate_Right Rs[4:0]
  shifter_carry_out = Rm[Rs[4:0] - 1]
*)

Definition so_ROR_reg (s : state) (m : processor_mode) (i : word)
  (Rm Rs : reg_num) : word * bool :=
  let Rm := reg_content s m Rm in
  let Rs := reg_content s m Rs in
  let Rs7 := bits 0 7 Rs in
  if zeq Rs7 0 then (Rm, is_set Cbit i)
  else let Rs4 := bits 0 4 Rs in
    if zeq Rs4 0 then (Rm, is_set 31 Rm)
    else (Rotate_Right Rm Rs4, is_set (pred (nat_of_Z Rs4)) Rm).

(****************************************************************************)
(* A5.1.13 Data-processing operands - Rotate right with extend (p. 457) *)
(****************************************************************************)

(*
shifter_operand = (C Flag Logical_Shift_Left 31) OR (Rm Logical_Shift_Right 1)
shifter_carry_out = Rm[0]
*)

Definition so_RRX (s : state) (m : processor_mode) (i : word) (Rm : reg_num)
  : word * bool :=
  let Rm := reg_content s m Rm in
    (or (Logical_Shift_Left (get Cbit i) w31) (Logical_Shift_Right Rm w1),
      is_set 0 Rm).

(****************************************************************************)
(* Semantics of a shifter operand *)
(****************************************************************************)

Definition shifter_operand_value_and_carry (s : state) (m : processor_mode)
  (i : word) (so : shifter_operand) : word * bool :=
  match so with
    | Imm rotate_imm immed_8 => so_imm i rotate_imm immed_8
    | Shift Rm h v =>
      match h, v with
        | LSL, ValImm shift_imm => so_LSL_imm s m i Rm shift_imm
        | LSL, ValReg Rs => so_LSL_reg s m i Rm Rs
        | LSR, ValImm shift_imm => so_LSR_imm s m i Rm shift_imm
        | LSR, ValReg Rs => so_LSR_reg s m i Rm Rs
        | ASR, ValImm shift_imm => so_ASR_imm s m i Rm shift_imm
        | ASR, ValReg Rs => so_ASR_reg s m i Rm Rs
        | ROR, ValImm shift_imm => so_ROR_imm s m i Rm shift_imm
        | ROR, ValReg Rs => so_ROR_reg s m i Rm Rs
      end
    | RRX r => so_RRX s m i r
  end.
