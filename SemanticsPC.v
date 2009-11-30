(**
SimSoC-Cert, a Coq library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Semantics of instructions using PseudoCode.
*)

Set Implicit Arguments.

Require Import State.
Require Import PseudoCode.
Require Import Bitvec.

Open Scope nat_scope.

Definition W0 := Word w0.
Definition W1 := Word w1.
Definition W15 := Word w15.

Definition dummy := w0.

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

Definition Adc (Sbit : bool) (Rd Rn : reg_num) (so : word) (s : state)
  (m : processor_mode) : result :=
  let word_of_var (k : nat) : word :=
    match k with
      | 0 => Sbit
      | 1 => Rd
      | 2 => Rn
      | 3 => so
      | _ => dummy
    end in
  let Sbit := Var 0 in
  let Rd := Var 1 in
  let Rn := Var 2 in
  let so := Var 3 in interp word_of_var m s
    (IfThen ConditionPassed
      (Seq (Affect (LReg Rd) (Add (Add (Reg Rn) so) (Flag Cbit)))
        (IfThenElse (BAnd (Eq Sbit W1) (Eq Rd W15))
          Affect_CPSR_SPSR
          (IfThen (Eq Sbit W1)
            (Seq (Affect (LFlag Nbit) (Bit 31 (Reg Rd)))
              (Seq (Affect (LFlag Zbit) (If (Eq (Reg Rd) W0) W1 W0))
                (Seq (Affect (LFlag Cbit)
                  (CarryFrom_add3 (Reg Rn) so (Flag Cbit)))
                (Affect (LFlag Vbit)
                  (OverflowFrom_add3 (Reg Rn) so (Flag Cbit)))))))))).

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

(*Definition Add (Sbit : bool) (Rd Rn : reg_num) (so : word) (s : state)
  (m : processor_mode) : result :=*)

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

(*Definition And (Sbit : bool) (Rd Rn : reg_num) (so : word) (c : bool)
  (s : state) (m : processor_mode) : result :=*)

(****************************************************************************)
(** A4.1.5 B, BL (p. 160) *)
(****************************************************************************)

(** <<
if ConditionPassed(cond) then
  if L == 1 then
    LR = address of the instruction after the branch instruction
  PC = PC + (SignExtend_30(signed_immed_24) << 2)
>>*)

(*Definition Bl (L : bool) (w : word) (s : state) (m : processor_mode) : result :=*)
