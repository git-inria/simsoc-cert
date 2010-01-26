(**
SimSoC-Cert, a Coq library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Semantics of instructions.
*)

Set Implicit Arguments.

Require Import State.
Require Import Bitvec.
Require Import Integers. Import Int.
Require Import Functions.
Require Import Coqlib.
Require Import Util.
Require Import Instructions.

(****************************************************************************)
(** A4.1.2 ADC (p. 154) *)
(****************************************************************************)

(** <<
if ConditionPassed(cond) then
  Rd = Rn + shifter_operand + C Flag
  if S == 1 and Rd == R15 then
    if CurrentModeHasSPSR() then
      CPSR = SPSR
    else UNPREDICTABLE
  else if S == 1 then
    N Flag = Rd[31]
    Z Flag = if Rd == 0 then 1 else 0
    C Flag = CarryFrom(Rn + shifter_operand + C Flag)
    V Flag = OverflowFrom(Rn + shifter_operand + C Flag)
>>*)

Definition Adc (cond : opcode) (Sbit : bool) (d n : reg_num) (so : word)
  (s : state) (m : processor_mode) : result :=
  let r := cpsr s in
  if ConditionPassed r cond then
    if Sbit then
      if zeq d 15 then
        match m with
          | usr | sys => None
          | exn e =>
            let Rn := reg_content s m n in
            let c := r[Cbit] in
            let v := add (add Rn so) c in
              Some (false, update_cpsr (spsr s e) (update_reg m d v s))
        end
      else
        let Rn := reg_content s m n in
        let c := r[Cbit] in
        let v := add (add Rn so) c in
          Some (true, update_cpsr
            (update_bit Vbit (OverflowFrom_add3 Rn so c)
            (update_bit Cbit (CarryFrom_add3 Rn so c)
            (update_bit Zbit (zne v 0)
            (update_bit Nbit v[31] r))))
            (update_reg m d v s))
    else
      let Rn := reg_content s m n in
      let c := r[Cbit] in
      let v := add (add Rn so) c in Some (zne d 15, update_reg m d v s)
  else Some (true, s).

(****************************************************************************)
(** A4.1.3 ADD (p. 156) *)
(****************************************************************************)

(** <<
if ConditionPassed(cond) then
  Rd = Rn + shifter_operand
  if S == 1 and Rd == R15 then
    if CurrentModeHasSPSR() then
      CPSR = SPSR
    else UNPREDICTABLE
  else if S == 1 then
    N Flag = Rd[31]
    Z Flag = if Rd == 0 then 1 else 0
    C Flag = CarryFrom(Rn + shifter_operand)
    V Flag = OverflowFrom(Rn + shifter_operand)
>>*)

Definition Add (cond : opcode) (Sbit : bool) (d n : reg_num) (so : word)
  (s : state) (m : processor_mode) : result :=
  let r := cpsr s in
  if ConditionPassed r cond then
    if Sbit then
      if zeq d 15 then
        match m with
          | usr | sys => None
          | exn e =>
            let Rn := reg_content s m n in
            let v := add Rn so in
              Some (false, update_cpsr (spsr s e) (update_reg m d v s))
        end
      else
        let Rn := reg_content s m n in
        let v := add Rn so in
          Some (true, update_cpsr
            (update_bit Vbit (OverflowFrom_add2 Rn so)
            (update_bit Cbit (CarryFrom_add2 Rn so)
            (update_bit Zbit (zne v 0)
            (update_bit Nbit v[31] r))))
            (update_reg m d v s))
    else
      let Rn := reg_content s m n in
      let v := add Rn so in Some (zne d 15, update_reg m d v s)
  else Some (true, s).

(****************************************************************************)
(** A4.1.4 AND (p. 158) *)
(****************************************************************************)

(** <<
if ConditionPassed(cond) then
  Rd = Rn AND shifter_operand
  if S == 1 and Rd == R15 then
    if CurrentModeHasSPSR() then
      CPSR = SPSR
    else UNPREDICTABLE
  else if S == 1 then
    N Flag = Rd[31]
    Z Flag = if Rd == 0 then 1 else 0
    C Flag = shifter_carry_out
    V Flag = unaffected
>>*)

Definition And (cond : opcode) (Sbit : bool) (d n : reg_num) (so : word)
  (c : bool) (s : state) (m : processor_mode) : result :=
  let r := cpsr s in
  if ConditionPassed r cond then
    if Sbit then
      if zeq d 15 then
        match m with
          | usr | sys => None
          | exn e =>
            let Rn := reg_content s m n in
            let v := and Rn so in
              Some (false, update_cpsr (spsr s e) (update_reg m d v s))
        end
      else
        let Rn := reg_content s m n in
        let v := and Rn so in
          Some (true, update_cpsr
            (update_bit_aux Cbit c
            (update_bit Zbit (zne v 0)
            (update_bit Nbit v[31] r)))
            (update_reg m d v s))
    else
      let Rn := reg_content s m n in
      let v := and Rn so in Some (zne d 15, update_reg m d v s)
  else Some (true, s).

(****************************************************************************)
(** A4.1.5 B, BL (p. 160) *)
(****************************************************************************)

(** <<
if ConditionPassed(cond) then
  if L == 1 then
    LR = address of the instruction after the branch instruction
  PC = PC + (SignExtend_30(signed_immed_24) << 2)
>>*)

Definition Bl (cond : opcode) (L : bool) (w : word) (s : state)
  (m : processor_mode) : result :=
  if ConditionPassed (cpsr s) cond then
    Some (false, update_reg m PC (Logical_Shift_Left (SignExtend 30 w) w2)
      (if L then update_reg m LR (next_inst_address s m) s else s))
  else Some (true, s).
