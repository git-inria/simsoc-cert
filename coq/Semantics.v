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

Definition update_NZCV N Z C V (cpsr : word) :=
  (update_bit Vbit V 
     (update_bit Cbit C
         (update_bit Zbit Z
            (update_bit Nbit N cpsr)))).

Definition update_NZC N Z C (cpsr : word) :=
     (update_bit Cbit C
         (update_bit Zbit Z
            (update_bit Nbit N cpsr))).

Definition Adc (cond : opcode) (Sbit : bool) (d n : reg_num) (so : word)
  (s : state) (m : processor_mode) : result :=
  let r := cpsr s in
  if ConditionPassed r cond then
    let Rn := reg_content s m n in
    let C_flag := r[Cbit] in
    let new_Rd := add (add Rn so) C_flag in
    let new_registers := update_reg m d new_Rd s in
    let not_branch := zne d 15 in
    if Sbit && (zeq d 15) then
        match SPSR_to_CPSR s m with
          | None => None
          | Some new_cpsr =>
              Some (not_branch, update_cpsr new_cpsr new_registers)
        end
      else if Sbit then
        let new_cpsr := 
               (update_NZCV
                         new_Rd[31]
                         (zeq new_Rd 0)
                         (CarryFrom_add3 Rn so C_flag)
                         (OverflowFrom_add3 Rn so C_flag)
                         r) in
          Some (not_branch, update_cpsr new_cpsr new_registers)
    else
      Some (not_branch, new_registers)
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
    let Rn := reg_content s m n in
    let new_Rd := add Rn so in
    let new_registers := update_reg m d new_Rd s in
    let not_branch := zne d 15 in
    if Sbit && (zeq d 15) then
        match SPSR_to_CPSR s m with
          | None => None
          | Some new_cpsr =>
              Some (not_branch, update_cpsr new_cpsr new_registers)
        end
      else if Sbit then
        let new_cpsr := 
               (update_NZCV 
                         new_Rd[31]
                         (zeq new_Rd 0)
                         (CarryFrom_add2 Rn so)
                         (OverflowFrom_add2 Rn so)
                         r) in
          Some (not_branch, update_cpsr new_cpsr new_registers)
    else
      Some (not_branch, new_registers)
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
    let Rn := reg_content s m n in
    let new_Rd := and Rn so in
    let new_registers := update_reg m d new_Rd s in
    let not_branch := zne d 15 in
    if Sbit && (zeq d 15) then
        match SPSR_to_CPSR s m with
          | None => None
          | Some new_cpsr =>
              Some (not_branch, update_cpsr new_cpsr new_registers)
        end
      else if Sbit then
        let new_cpsr := 
          update_NZC new_Rd[31]
                     (zeq new_Rd 0)
                     c r in
          Some (not_branch, update_cpsr new_cpsr new_registers)
    else
      Some (not_branch, new_registers)
  else Some (true, s).

(****************************************************************************)
(** A4.1.106 SUB (p. 358) *)
(****************************************************************************)
(** <<
if ConditionPassed(cond) then
    Rd = Rn - shifter_operand
    if S == 1 and Rd == R15 then
        if CurrentModeHasSPSR() then
            CPSR = SPSR
        else UNPREDICTABLE
    else if S == 1 then
        N Flag = Rd[31]
        Z Flag = if Rd == 0 then 1 else 0
        C Flag = NOT BorrowFrom(Rn - shifter_operand)
        V Flag = OverflowFrom(Rn - shifter_operand)
>>*)

Definition Sub (cond : opcode) (Sbit : bool) (d n : reg_num) (so : word)
  (c : bool) (s : state) (m : processor_mode) : result :=
  let r := cpsr s in
  if ConditionPassed r cond then
    let Rn := reg_content s m n in
    let new_Rd := sub Rn so in
    let new_registers := update_reg m d new_Rd s in
    let not_branch := zne d 15 in
    if Sbit && (zeq d 15) then
	match SPSR_to_CPSR s m with
	  | None => None
	  | Some new_cpsr =>
	      Some (not_branch, update_cpsr new_cpsr new_registers)
	end
      else if Sbit then
        let new_cpsr := 
               (update_NZCV
                         new_Rd[31]
                         (zeq new_Rd 0)
                         (not (BorrowFrom_sub Rn so))
                         (OverflowFrom_sub Rn so)
                         r) in
          Some (not_branch, update_cpsr new_cpsr new_registers)
      else
        Some (not_branch, new_registers)
    else Some (true, s).

(****************************************************************************)
(** A4.1.5 B, BL (p. 160) *)
(****************************************************************************)

(** <<
if ConditionPassed(cond) then
  if L == 1 then
    LR = address of the instruction after the branch instruction
  PC = PC + (SignExtend_30(signed_immed_24) << 2)

1: if ConditionPassed(cond) then
2: LR = if L == 1 then address of the instruction after the branch instruction
        else LR
4:  PC = PC + (SignExtend_30(signed_immed_24) << 2)
>>*)

Definition Bl (cond : opcode) (L : bool) (w : word) (s : state)
  (m : processor_mode) : result :=
  if ConditionPassed (cpsr s) cond then
    Some (false, update_reg m PC (Logical_Shift_Left (SignExtend 30 w) w2)
      (if L then update_reg m LR (next_inst_address s m) s else s))
  else Some (true, s).

Definition Bl_bis (cond : opcode) (L : bool) (w : word) (s : state)
  (m : processor_mode) : result :=
(*1*)  if ConditionPassed (cpsr s) cond then
(*2*)    let old_LR := reg_content s m LR in
(*2*)    let new_LR := if L then next_inst_address s m else old_LR in
(*4*)    let old_PC := reg_content s m PC in
(*4*)    let new_PC := add old_PC (Logical_Shift_Left (SignExtend 24 w) w2) in
(* *)    Some (false, update_reg m PC new_PC (update_reg m LR new_LR s))
(*1*)  else
(*1*)    Some (true, s).

(****************************************************************************)
(** A4.1.8 BLX(1) (p. 166) *)
(****************************************************************************)

(**<<
LR = address of the instruction after the BLX instruction
CPSR T bit = 1
PC = PC + (SignExtend(signed_immed_24) << 2) + (H << 1)
>>*)

Definition Blx (w : word) (s : state) (m : processor_mode) : result :=
  let old_LR := reg_content s m LR in
  let new_LR := next_inst_address s m in 
  let old_PC := reg_content s m PC in
  let new_PC := add (add old_PC (Logical_Shift_Left (SignExtend 24 w) w2))
                    (Logical_Shift_Left w[24] w1) in
  Some (false, update_reg m PC new_PC
               (update_cpsr (update_bit Tbit true (cpsr s))
               (update_reg m LR new_LR s))).

(****************************************************************************)
(** A4.1.10 BX (p. 170) *)
(****************************************************************************)

(**<<
if ConditionPassed(cond) then
    CPSR T bit = Rm[0]
    PC = Rm AND 0xFFFFFFFE
>>*)

Definition Bx (cond : opcode) (rm : reg_num) (s : state) (m : processor_mode)
  : result :=
  let r := cpsr s in
  if ConditionPassed r cond then
    let Rm := reg_content s m rm in
    let old_PC := reg_content s m PC in
    let new_PC := and Rm (sub max w1) in
    Some(false, update_reg m PC new_PC 
                (update_cpsr (update_bit Tbit Rm[0] (cpsr s)) s))
  else Some(true, s).

(****************************************************************************)
(** A4.1.13 CLZ (p. 175) *)
(****************************************************************************)

(** <<
if Rm == 0
     Rd = 32
else
     Rd = 31 - (bit position of most significant'1' in Rm)
>>*)

Fixpoint count (w : word) (i: nat) {struct i}: word :=
match i with
| O => repr 0
| S i' => 
if is_set 31 w then repr (Z_of_nat i')
  else count (shl w w1) i'
end.

Definition Clz (cond : opcode) (rm rd : reg_num) (w : word) (s : state) 
  (m : processor_mode) : result :=
  let r := cpsr s in
  if ConditionPassed r cond then
  let not_branch := zne rd 15 in
    if (zne rd 15) && (zne rm 15) then
      let Rm := reg_content s m rm in
      let Rd := reg_content s m rd in
      if zeq Rm 0 then
        Some (not_branch, update_reg m rd (repr 32) s)
      else Some (not_branch, update_reg m rd (sub w31 (count w 32)) s)
    else None
  else Some (true, s).

(****************************************************************************)
(** A4.1.15 CMP (p. 178) *)
(****************************************************************************)

(** <<
if ConditionPassed(cond) then
    alu_out = Rn - shifter_operand
    N Flag = alu_out[31]
    Z Flag = if alu_out == 0 then 1 else 0
    C Flag = NOT BorrowFrom(Rn - shifter_operand)
    V Flag = OverflowFrom(Rn - shifter_operand)
>>*)

Definition Cmp (cond : opcode) (n : reg_num) (so : word) (s : state)
  (m : processor_mode) : result :=
  let r := cpsr s in
  let Rn := reg_content s m n in
  let alu_out := sub Rn so in
  if ConditionPassed r cond then
        let new_cpsr := 
               (update_NZCV
                         alu_out[31]
                         (zeq alu_out 0)
                         (not (BorrowFrom_sub Rn so))
                         (OverflowFrom_sub Rn so)
                         r) in
          Some (true, update_cpsr new_cpsr s)
   else
     Some (true, s).

(****************************************************************************)
(** A4.1.35 MOV (p. 218) *)
(****************************************************************************)

(**<<
if ConditionPassed(cond) then
    Rd = shifter_operand
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

Definition Mov (cond : opcode) (Sbit : bool) (d : reg_num) (so : word)
  (c : bool) (s : state) (m : processor_mode) : result :=
  let r := cpsr s in
  if ConditionPassed r cond then
    let new_Rd := so in
    let new_registers := update_reg m d new_Rd s in
    let not_branch := zne d 15 in
    if Sbit && (zeq d 15) then
      match SPSR_to_CPSR s m with
        | None => None
        | Some new_cpsr => 
            Some (not_branch, update_cpsr new_cpsr new_registers)
       end
    else if Sbit then
          Some (true, update_cpsr 
            (update_bit_aux Cbit c
            (update_bit Zbit (zeq new_Rd 0)
            (update_bit Nbit new_Rd[31] r)))
            (update_reg m d new_Rd s))    
         else Some(not_branch, new_registers)
  else Some (true, s).

(****************************************************************************)
(** A4.1.40 MUL (p. 230) *)
(****************************************************************************)

(**<<
if ConditionPassed(cond) then
    Rd = (Rm * Rs)[31:0]
    if S == 1 then
        N Flag = Rd[31]
        Z Flag = if Rd == 0 then 1 else 0
        C Flag = unaffected in v5 and above, UNPREDICTABLE in v4 and earlier
        V Flag = unaffected
>>*)

Definition Mul (cond : opcode) (Sbit : bool) (rd rm rs: reg_num)
  (s : state) (m : processor_mode) : result :=
  let r := cpsr s in
  if ConditionPassed r cond then
    let Rm := reg_content s m rm in
    let Rs := reg_content s m rs in
    let new_Rd := (mul Rm Rs)[31#0] in
    let new_registers := update_reg m rd new_Rd s in
    let not_branch := zne rd 15 in
    if Sbit then
      Some (not_branch, update_cpsr
        (update_bit Zbit (zeq new_Rd 0)
        (update_bit Nbit new_Rd[31] r))
        (update_reg m rd new_Rd s))
    else Some (not_branch, new_registers)
  else Some(true, s).

(****************************************************************************)
(** A4.1.43 PKHBT (p. 236) *)
(****************************************************************************)

(**<<
if ConditionPassed(cond) then
    Rd[15:0] = Rn[15:0]
    Rd[31:16] = (Rm Logical_Shift_Left shift_imm)[31:16]
>>*)

Definition Pkhbt (cond : opcode) (rd rn rm : reg_num) (shift_imm : word)
  (s : state) (m : processor_mode) : result :=
  let r := cpsr s in
  if ConditionPassed r cond then
    let Rn := reg_content s m rn in
    let Rm := reg_content s m rm in
    let Rd := reg_content s m rd in
    let new_Rdl := update_bits 15 0 Rn Rd in
    let new_Rd := update_bits 31 16 
	           (Logical_Shift_Left Rm shift_imm)[31#16] new_Rdl in
    let not_branch := zne rd 15 in
    Some(not_branch, update_reg m rd new_Rd s)
  else Some(true, s).

(****************************************************************************)
(** A4.1.43 PKHTB (p. 239) *)
(****************************************************************************)

(**<<
if ConditionPassed(cond) then
    if shift_imm == 0 then           /* ASR #32 case */
         if Rm[31] == 0 then
              Rd[15:0] = 0x0000
         else
              Rd[15:0] = 0xFFFF
    else
         Rd[15:0] = (Rm Arithmetic_Shift_Right shift_imm)[15:0]
    Rd[31:16] = Rn[31:16]
>>*)

(* NOT FINISHED *)

(*
Definition Pkhtb (cond : pocode) (rd rn rm : reg_num) (shift_imm : word)
  (s : state) (m : processor_mode) : result :=
  let r := cpsr s in
*)
