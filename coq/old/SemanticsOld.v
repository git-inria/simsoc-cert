(**
SimSoC-Cert, a toolkit for generating certified processor simulators.
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
Require Import IntSemantics.

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
  (s : state) : result :=
  intOp true s
  (IntIf (ConditionPassed (cpsr s) cond)
    (IntBlock 
      (Affect_reg d (add (add (reg_content s n) so) (cpsr s)[Cbit]))
      (IntIfElse (Sbit && (zeq d 15))
        (IntIfElse (CurrentModeHasSPSR s)
          (Affect_cpsr (cpsr s))
          (Unpredictable))
        (IntIf (Sbit)
          (IntBlock
            (Affect_cpsr_bit Nbit (reg_content s d)[31] (cpsr s))
            (IntBlock 
              (Affect_cpsr_bit Zbit 
                (if (zeq (reg_content s d) 0) then w1 else w0)
                (cpsr s))
              (IntBlock
                (Affect_cpsr_bit Cbit
                  ((CarryFrom_add3 (reg_content s n) so (cpsr s)[Cbit]))
                  (cpsr s))
                (Affect_cpsr_bit Vbit
                  (OverflowFrom_add3 (reg_content s n) so (cpsr s)[Cbit])
                  (cpsr s))))))))).

(*
Definition Adc (cond : opcode) (Sbit : bool) (d n : reg_num) (so : word)
  (s : state) (m : processor_mode(*FIXME:REMOVE*)) : result :=

(fun b s => IntIf (ConditionPassed (cpsr s) cond)
  (fun b s => IntBlock(
    (fun b s =>
      Affect_reg s d (add (add (reg_content s n) so) (cpsr s)[Cbit]))
    (fun b s =>
      (*intif (S = 1 and d = 15)*)
      IntIf (Sbit && (zeq d 15))
        (fun b s =>
           IntIfElse (CurrentModeHasSPSR s)
             (fun b s => Affect_cpsr s (spsr s))
             (fun b s => None))
        (fun b s =>
          IntIf (Sbit)
           (*intif (S = 1)*)
             (fun b s => IntBlock(
                (fun b s => Affect_cpsr_bit* s Nbit (reg_content s d)[31])
                (fun b s => Affect_cpsr_bit s Zbit
                  (if reg_content s d = 0 then 1 else 0))
                (fun b s => Affect_cpsr_bit s Cbit 
                  (CarryFrom_add3 (reg_content s n) so (cpsr s)[Cbit]))
                (fun b s => Affect_cpsr_bit s Vbit
                  (OverflowFrom_add3 (reg_content s n) so (cpsr s)[Cbit]))))
             (fun b s => Some (b, s)))))
  (fun b s => Some (b, s)))))
  true s.

  match affect_reg d (add (add (reg_content s m n) so) r[Cbit]) s with
  | None => None
  | Some (b, s') =>
    if S == 1 and d == 15 then
      if CurrentModeHasSPSR s' then
        affect_cpsr spsr s' 
      else
        None
    else
      if S == 1 then
        affect_N_flag Rd[31] s'
      else Some (b, s')
else Some (true, s)

*)


Definition update_NZCV N Z C V (cpsr : word) :=
  (update_bit Vbit V 
     (update_bit Cbit C
         (update_bit Zbit Z
            (update_bit Nbit N cpsr)))).

Definition update_NZC N Z C (cpsr : word) :=
     (update_bit Cbit C
         (update_bit Zbit Z
            (update_bit Nbit N cpsr))).
(*
Definition Adc (cond : opcode) (Sbit : bool) (d n : reg_num) (so : word)
  (s : state) (m : processor_mode(*FIXME:REMOVE*)) : result :=

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
    else
      if Sbit then
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
*)
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
  (s : state) : result :=
  intOp true s
  (IntIf (ConditionPassed (cpsr s) cond)
    (IntBlock 
      (Affect_reg d (add (reg_content s n) so))
      (IntIfElse (Sbit && zeq d 15)
        (IntIfElse (CurrentModeHasSPSR s)
          (Affect_cpsr (cpsr s))
          (Unpredictable))
      (IntIf (Sbit)
          (IntBlock
            (Affect_cpsr_bit Nbit (reg_content s d)[31] (cpsr s))
            (IntBlock 
              (Affect_cpsr_bit Zbit 
                (if (zeq (reg_content s d) 0) then w1 else w0)
                (cpsr s))
              (IntBlock
                (Affect_cpsr_bit Cbit
                  (CarryFrom_add2 (reg_content s n) so)
                  (cpsr s))
                (Affect_cpsr_bit Vbit
                  (OverflowFrom_add2 (reg_content s n) so)
                  (cpsr s))))))))).


(*
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
*)
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
  (s : state) : result :=
  intOp true s
  (IntIf (ConditionPassed (cpsr s) cond)
    (IntBlock 
      (Affect_reg d (and (reg_content s n) so))
      (IntIfElse (Sbit && zeq d 15)
        (IntIfElse (CurrentModeHasSPSR s)
          (Affect_cpsr (cpsr s))
          (Unpredictable))
      (IntIf (Sbit)
          (IntBlock
            (Affect_cpsr_bit Nbit (reg_content s d)[31] (cpsr s))
            (IntBlock 
              (Affect_cpsr_bit Zbit 
                (if (zeq (reg_content s d) 0) then w1 else w0)
                (cpsr s))
              (Affect_cpsr_bit Cbit so (cpsr s)))))))).


(*
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
*)
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
  (s : state) : result :=
  intOp true s
  (IntIf (ConditionPassed (cpsr s) cond)
    (IntBlock 
      (Affect_reg d (sub (reg_content s n) so))
      (IntIfElse (Sbit && zeq d 15)
        (IntIfElse (CurrentModeHasSPSR s)
          (Affect_cpsr (cpsr s))
          (Unpredictable))
        (IntIf (Sbit)
          (IntBlock
            (Affect_cpsr_bit Nbit (reg_content s d)[31] (cpsr s))
            (IntBlock 
              (Affect_cpsr_bit Zbit 
                (if (zeq (reg_content s d) 0) then w1 else w0)
                (cpsr s))
              (IntBlock
                (Affect_cpsr_bit Cbit
                  (not (BorrowFrom_sub (reg_content s n) so))
                  (cpsr s))
                (Affect_cpsr_bit Vbit
                  (OverflowFrom_sub (reg_content s n) so)
                  (cpsr s))))))))).
(*
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
*)
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
(*
Definition Bl (cond : opcode) (L : bool) (w : word) (s : state)
  (m : processor_mode) : result :=
  if ConditionPassed (cpsr s) cond then
    Some (false, update_reg m PC (Logical_Shift_Left (SignExtend 30 w) w2)
      (if L then update_reg m LR (next_inst_address s m) s else s))
  else Some (true, s).
*)

Definition Bl (cond : opcode) (L : bool) (w : word) (s : state)
  :result :=
  intOp true s
  (IntIf (ConditionPassed (cpsr s) cond)
    (IntBlock
      (IntIf (L)
        (Affect_reg LR (next_inst_address s)))
      (Affect_reg PC (add (reg_content s PC) 
        (Logical_Shift_Left (SignExtend_24to30 w) w2))))).

(*
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
*)
(****************************************************************************)
(** A4.1.8 BLX(1) (p. 166) *)
(****************************************************************************)

(**<<
LR = address of the instruction after the BLX instruction
CPSR T bit = 1
PC = PC + (SignExtend(signed_immed_24) << 2) + (H << 1)
>>*)
(*
(* length of si24 = 24 *)
Definition Blx (si24 : word) (Hbit : bool) (s : state) (m : processor_mode) :
  result :=
  let old_LR := reg_content s m LR in
  let new_LR := next_inst_address s m in 
  let old_PC := reg_content s m PC in
  let new_PC := add (add old_PC (Logical_Shift_Left (SignExtend 24 si24) w2))
                    (Logical_Shift_Left (word_of_bool Hbit) w1) in
  Some (false, update_reg m PC new_PC
               (update_cpsr (update_bit Tbit true (cpsr s))
               (update_reg m LR new_LR s))).
*)
(****************************************************************************)
(** A4.1.10 BX (p. 170) *)
(****************************************************************************)

(**<<
if ConditionPassed(cond) then
    CPSR T bit = Rm[0]
    PC = Rm AND 0xFFFFFFFE
>>*)
(*
Definition Bx (cond : opcode) (rm : reg_num) (s : state) (m : processor_mode)
  : result :=
  let r := cpsr s in
  if ConditionPassed r cond then
    let Rm := reg_content s m rm in
    let old_PC := reg_content s m PC in
    let new_PC := and Rm w0xFFFFFFFE in
    Some(false, update_reg m PC new_PC 
                (update_cpsr (update_bit Tbit Rm[0] r) s))
  else Some(true, s).
*)
(****************************************************************************)
(** A4.1.13 CLZ (p. 175) *)
(****************************************************************************)

(** <<
if Rm == 0
     Rd = 32
else
     Rd = 31 - (bit position of most significant'1' in Rm)
>>*)

(* FIXME: if Rd is PC then the result should be UNPREDICTABLE *)

(* FIXME: if Rm is PC then the result should be UNPREDICTABLE *)
(*
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
    if (not_branch) && (zne rm 15) then
      let Rm := reg_content s m rm in
      let Rd := reg_content s m rd in
      if zeq Rm 0 then
        Some (not_branch, update_reg m rd (repr 32) s)
      else Some (not_branch, update_reg m rd (sub w31 (count w 32)) s)
    else None
  else Some (true, s).
*)
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
(*
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
*)
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
(*
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
*)
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
(*
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
*)
(****************************************************************************)
(** A4.1.43 PKHBT (p. 236) *)
(****************************************************************************)

(**<<
if ConditionPassed(cond) then
    Rd[15:0] = Rn[15:0]
    Rd[31:16] = (Rm Logical_Shift_Left shift_imm)[31:16]
>>*)
(*
Definition Pkhbt (cond : opcode) (rd rn rm : reg_num) (shift_imm : word)
  (s : state) (m : processor_mode) : result :=
  let r := cpsr s in
  if ConditionPassed r cond then
    let Rn := reg_content s m rn in
    let Rm := reg_content s m rm in
    let Rd := reg_content s m rd in
    let new_Rdl := update_bits 15 0 (get_half_0 Rn) Rd in
    let new_Rd := update_bits 31 16 
	          (get_half_1 (Logical_Shift_Left Rm shift_imm)) new_Rdl in
    let not_branch := zne rd 15 in
    Some(not_branch, update_reg m rd new_Rd s)
  else Some(true, s).
*)
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

(****************************************************************************)
(** A4.1.16 CPS (p. 179) *)
(****************************************************************************)

(**<<  
if InAPrivilegedMode() then
    if imod[1] == 1 then
        if A == 1 then CPSR[8] = imod[0]
        if I == 1 then CPSR[7] = imod[0]
        if F == 1 then CPSR[6] = imod[0]
    /* else no change to the mask */
    if mmod == 1 then
        CPSR[4:0] = mode
>>*)

(*NOT FINISHED*)
(*
Definition Cps (w : word)(s : state) (m : processor_mode) : result :=
   let r := cpsr s in
   if InAPrivilegedMode m then
     if zeq w[19] 1 then
       Some(true, 
           update_cpsr (if zeq w[Abit] 1 then (update_bit 6 r w[18])
            else (if zeq w[Ibit] 1 then (update_bit 7 r w[18])
              else (if zeq w[Abit] 1 then (update_bit 8 r w[18])
                else r))) s)
     else Some(true, s)
   else Some(true, s).
*)
  
(****************************************************************************)
(** A4.1.23 LDR (p. 193) *)
(****************************************************************************)

(**<<
MemoryAccess(B-bit, E-bit)
if ConditionPassed(cond) then
    if (CP15_reg1_Ubit == 0) then
         data = Memory[address,4] Rotate_Right (8 * address[1:0])
    else      /* CP15_reg_Ubit == 1 */
         data = Memory[address,4]
    if (Rd is R15) then
         if (ARMv5 or above) then
              PC = data AND 0xFFFFFFFE
              T Bit = data[0]
         else
              PC = data AND 0xFFFFFFFC
    else
         Rd = data
>>*)

(*NOT FINISHED*)
(*Put in the right file*)
(*
Definition MemoryAccess (Bbit : bool) (Ebit : bool) : 
  option endian_model :=
  match Bbit, Ebit with
    | false, false => Some LowE
    | false, true => Some BE_8
    | true, false => Some BE_32
    | true, true => None
  end.

Inductive size : Set := l1 | l2 | l4.

Definition Memory (ad : address) (sz : size) (s : state) : word :=
  match sz with
    | l1 => zero_ext 32 (get_byte_0 (mem s ad))
    | l2 => zero_ext 32 (get_half_0 (mem s ad))
    | l4 => zero_ext 32 (mem s ad)
  end.
*)
(*
Definition Ldr (cond : opcode) (Ubit : bool) (d : reg_num)
  (am : addressing_mode) (s : state) (m : processor_mode) 
  (ad : address) : result :=
  let r := cpsr s in
  let not_branch := zeq d 15 in
  let data := w0 in
  let Rd := reg_content s m d in
  let old_PC := reg_content s m PC in
  let new_PC1 := and data w0xFFFFFFFE in
  let new_PC2 := and data w0xFFFFFFFC in

    if ConditionPassed r cond then
      if not Ubit then
        data =  Rotate_Right (Memory ad l4 s) (mul 8 ad[1#0])
      else
        data = Memory ad l4 s
      if not_branch then
         Some(not_branch, update_reg m PC new_PC1
               (update_cpsr (update_bit Tbit data[0] r) s))
      else Some(true, s)
    else
      Some(false, update_reg m d Rd s).    
*)
