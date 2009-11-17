(**
SimSoC-Cert, a Coq library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2009-11-12

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.
*)

Set Implicit Arguments.

Require Import ZArith.
Require Import Bool.
Require Import Coqlib.
Require Import Integers. Import Int.

Open Scope Z_scope.

Lemma between_dec : forall a x b, {a <= x <= b}+{~(a <= x <= b)}.

Proof.
intros. case (Z_le_dec a x); intro. case (Z_le_dec x b); intro.
left. auto. right. intros [h1 h2]. contradiction.
right. intros [h1 h2]. contradiction.
Defined.

(****************************************************************************)
(* Architecture versions (p. 13) *)
(****************************************************************************)

Inductive version : Type :=
(* All architecture names prior to ARMv4 are now OBSOLETE *)
| ARMv4 | ARMv4T
| ARMv5T | ARMv5TExP (*for legacy reasons only*) | ARMv5TE | ARMv5TEJ
| ARMv6.

(****************************************************************************)
(* Chapter A2 - Programmers’ Model *)
(****************************************************************************)

(****************************************************************************)
(* Processor configuration *)
(****************************************************************************)

(* A2.4.3 Reading the program counter (p. 47) *)

Inductive store_pc_offset_value : Type := O8 | O12.

Definition store_pc_offset (v : store_pc_offset_value) : Z :=
  match v with
    | O8 => 8
    | O12 => 12
  end.
 
(* A2.6.5 Abort models *)

Inductive abort_model : Type := Restored | Updated.

(* All parameters gathered *)

Module Type CONFIG.
  Variable version : version.
  Variable store_pc_offset : store_pc_offset_value.
  Variable ve_irq_normal_address : Z. (* A2.6 Exceptions (p. 54) *)
  Variable ve_fiq_normal_address : Z.
  Variable ve_irq_high_vector_address : Z.
  Variable ve_fiq_high_vector_address : Z.
  Variable abort_model : abort_model.
  Variable imprecise_aborts_max : Z. (* A2.6.7 Imprecise data aborts (p. 61) *)
  Variable be32_support : bool.
    (* A2.7.3 Endian configuration and control (p. 72) *)
End CONFIG.

(****************************************************************************)
(* A2.1 Datatypes (p. 41) *)
(****************************************************************************)

Definition word := int.

Definition is_not_zero w := negb (zeq (intval w) 0).

(* Tell if the i-th bit of a word is set *)
(*REMOVE:Definition bit w i := bits_of_Z wordsize (intval w) i.*)

(* Sub-word between bit [i] and bit [j], assuming i <= j *)
(*REMOVE:Definition subintval w i j :=
  Z_of_bits wordsize (fun k => if zle i k && zle k j then bit w k else false).*)

(*FIXME: replace bits by generalizing in Integers the type int by
taking wordsize as a parameter?*)
Record bits (n : nat) : Type := mk_bits {
  bits_val :> Z;
  bits_prf : 0 <= bits_val < two_power_nat n
}.

Lemma bits_eqdec : forall n (b1 b2 : bits n), {b1=b2}+{~b1=b2}.

Proof.
intros n [v1 p1] [v2 p2]. case (zeq v1 v2); intro.
left. subst. rewrite (proof_irrelevance _ p1 p2). auto.
right. intro h. inversion h. contradiction.
Qed.

(*FIXME: do we need to define types for bytes and halfwords?*)
Definition halfword := bits 16.
Definition byte := bits 8.

(****************************************************************************)
(* A2.2 Processor modes (p. 410) *)
(****************************************************************************)

Module Arm (C : CONFIG).

Inductive processor_exception_mode : Type := fiq | irq | svc | abt | und.

Inductive processor_mode : Type :=
  usr | sys | exn (m : processor_exception_mode).

Definition CurrentModeHasSPSR (m : processor_mode) : bool :=
  match m with
    | usr | sys => false
    | _ => true
  end.

(****************************************************************************)
(* A2.3 Registers (p. 42) *)
(* A2.4 General-purpose registers (p. 44) *)
(****************************************************************************)

Definition register_number := bits 4.

Definition is_eq (Rd : register_number) (x : Z) : bool := zeq (bits_val Rd) x.

Inductive physical_register : Type :=
| R (r : register_number)
| R_svc (v : Z) (h : 13 <= v <= 14)
| R_abt (v : Z) (h : 13 <= v <= 14)
| R_und (v : Z) (h : 13 <= v <= 14)
| R_irq (v : Z) (h : 13 <= v <= 14)
| R_fiq (v : Z) (h : 8 <= v <= 14).

Definition physical_registers := physical_register -> word.

Lemma physical_register_eqdec : forall x y : physical_register, {x=y}+{~x=y}.

Proof.
destruct x; destruct y; intros; try (right; discriminate).
destruct (bits_eqdec r r0). subst. auto.
right. intro h. inversion h. contradiction.
destruct (zeq v v0). subst. rewrite (proof_irrelevance _ h0 h). auto.
right. intro p. inversion p. contradiction.
destruct (zeq v v0). subst. rewrite (proof_irrelevance _ h0 h). auto.
right. intro p. inversion p. contradiction.
destruct (zeq v v0). subst. rewrite (proof_irrelevance _ h0 h). auto.
right. intro p. inversion p. contradiction.
destruct (zeq v v0). subst. rewrite (proof_irrelevance _ h0 h). auto.
right. intro p. inversion p. contradiction.
destruct (zeq v v0). subst. rewrite (proof_irrelevance _ h0 h). auto.
right. intro p. inversion p. contradiction.
Qed.

Definition phy_reg_of_exn_mode (m : processor_exception_mode)
  (k : register_number) : physical_register :=
  match m with
    | svc =>
      match between_dec 13 k 14 with
        | left h => R_svc h
        |   => R k
      end
    | abt =>
      match between_dec 13 k 14 with
        | left h => R_abt h
        |   => R k
      end
    | und =>
      match between_dec 13 k 14 with
        | left h => R_und h
        |   => R k
      end
    | irq =>
      match between_dec 13 k 14 with
        | left h => R_irq h
        |   => R k
      end
    | fiq =>
      match between_dec 8 k 14 with
        | left h => R_fiq h
        |   => R k
      end
  end.

Definition phy_reg_of_mode (m : processor_mode) (k : register_number)
  : physical_register :=
  match m with
    | usr | sys => R k
    | exn e => phy_reg_of_exn_mode e k
  end.

(****************************************************************************)
(* A2.5 Program status registers (p. 49) *)
(****************************************************************************)

Definition status_register := word.

(* Condition code flags (p. 49) *)

Definition Nmask := (*bit[31]*) repr 2147483648.
Definition Nbit r := and r Nmask.
Definition set_N r := is_not_zero (Nbit r).

Definition Zmask := (*bit[30]*) repr 1073741824.
Definition Zbit r := and r Zmask.
Definition set_Z r := is_not_zero (Zbit r).

Definition Cmask := (*bit[29]*) repr 536870912.
Definition Cbit r := and r Cmask.
Definition set_C r := is_not_zero (Cbit r).

Definition Vmask := (*bit[28]*) repr 268435456.
Definition Vbit r := and r Vmask.
Definition set_V r := is_not_zero (Vbit r).

(* The Q flag (p. 51) *)

Definition Qmask := (*bit[27]*) repr 134217728.
Definition Qbit r := and r Qmask.
Definition set_Q r := is_not_zero (Qbit r).

(* The GE bits (p. 51) *)

Definition GEmask := (*bits[16:19]*) repr 983040.
Definition GEbits r := and r GEmask.

(* The E bit (p. 51) *)

Definition Emask := (*bit[9]*) repr 512.
Definition Ebit r := and r Emask.
Definition set_E r := is_not_zero (Ebit r).

(* The interrupt disable bits (p. 52) *)

Definition Amask := (*bit[8]*) repr 256.
Definition Abit r := and r Amask.
Definition set_A r := is_not_zero (Abit r).

Definition Imask := (*bit[7]*) repr 128.
Definition Ibit r := and r Imask.
Definition set_I r := is_not_zero (Ibit r).

Definition Fmask := (*bit[6]*) repr 64.
Definition Fbit r := and r Fmask.
Definition set_F r := is_not_zero (Fbit r).

(* Mode bits (p. 52) *)

Definition Mmask := (*bits[0:4]*) repr 15.
Definition Mbits r := and r Mmask.

Definition mode (r : status_register) : option processor_mode :=
  match intval (Mbits r) with
    | (*0b10000*) 16 => Some usr
    | (*0b10001*) 17 => Some (exn fiq)
    | (*0b10010*) 18 => Some (exn irq)
    | (*0b10011*) 19 => Some (exn svc)
    | (*0b10111*) 23 => Some (exn abt)
    | (*0b11011*) 27 => Some (exn und)
    | (*0b11111*) 31 => Some sys
    | _ => None
  end.

(* The T and J bits (p. 53) *)

Definition Tmask := (*bit[5]*) repr 32.
Definition Tbit r := and r Tmask.
Definition set_T r := is_not_zero (Tbit r).

Definition Jmask := (*bit[24]*) repr 16777216.
Definition Jbit r := and r Jmask.
Definition set_J r := is_not_zero (Jbit r).

(****************************************************************************)
(* A2.6 Exceptions (p. 54) *)
(****************************************************************************)

Inductive exception : Type :=
  Reset | UndIns | SoftInt | ImpAbort | PFAbort | DataAbort | IRQ | FIQ.

Definition exception_mode (e : exception) : processor_exception_mode :=
  match e with
    | Reset => svc
    | UndIns => und
    | SoftInt => svc
    | ImpAbort => abt
    | PFAbort => abt
    | DataAbort => abt
    | IRQ => irq
    | FIQ => fiq
  end.

(*FIXME: Definition exception_handler_address (e : exception) : BinInt.Z :=
  match C.use_high_vectors with
    | false =>
      match e with
        | Reset =>     (*0x00000000*)  0
        | UndIns =>    (*0x00000004*)  4
        | SoftInt =>   (*0x00000008*)  8
        | PFAbort =>   (*0x0000000C*) 12
        | DataAbort => (*0x00000010*) 16
(*FIXME: depends on VE bit in the system control coprocessor *)
        | IRQ =>       (*0x00000018*) 24
        | FIQ =>       (*0x0000001C*) 28
      end
    | true =>
      match e with
        | Reset =>     (*0xFFFF0000*) 4294901760
        | UndIns =>    (*0xFFFF0004*) 4294901764
        | SoftInt =>   (*0xFFFF0008*) 4294901768
        | PFAbort =>   (*0xFFFF000C*) 4294901772
        | DataAbort => (*0xFFFF0010*) 4294901776
(*FIXME: depends on VE bit in the system control coprocessor *)
        | IRQ =>       (*0xFFFF0018*) 4294901784
        | FIQ =>       (*0xFFFF001C*) 4294901788
      end
  end.*)

(* Exception priorities (p. 63) *)
Definition priority (e : exception) : BinInt.Z :=
  match e with
    | Reset => 1 (* highest *)
    | DataAbort => 2
    | FIQ => 3
    | IRQ => 4
    | ImpAbort => 5
    | PFAbort => 6
    | UndIns | SoftInt => 7 (* lowest *)
  end.

(****************************************************************************)
(* A2.7 Endian support (p. 68) *)
(****************************************************************************)

Definition address := bits 30.

Definition address_eqdec := @bits_eqdec 30.

Definition memory := address -> word.

(****************************************************************************)
(* A2.8 Unaligned access support (p. 76) *)
(****************************************************************************)

(****************************************************************************)
(* A2.9 Unaligned access support (p. 76) *)
(****************************************************************************)

(****************************************************************************)
(* A2.10 The Jazelle Extension *)
(****************************************************************************)

(****************************************************************************)
(* A2.11 Saturated integer arithmetic *)
(****************************************************************************)

(****************************************************************************)
(* ARM state *)
(****************************************************************************)

Record state : Type := mk_state {
  cpsr : status_register; (* Current program status register *)
  spsr : processor_exception_mode -> status_register;
    (* Saved program status registers *)
  reg : physical_registers;
  mem : memory;
  exns : list exception (* Raised exceptions *)
}.

(*FIXME: does not work :-(
Notation "s .cpsr" := (cpsr s) (at level 2, left associativity).
Notation "s .spsr" := (spsr s) (at level 2, left associativity).
Notation "s .reg" := (reg s) (at level 2, left associativity).
Notation "s .mem" := (mem s) (at level 2, left associativity).
Notation "s .exns" := (exns s) (at level 2, left associativity).*)

Section update.

Variables (A : Type) (eqdec : forall x y : A, {x=y}+{~x=y}) (B : Type).

Definition update (f : A -> B) (a : A) (b : B) : A -> B :=
  fun x => if eqdec x a then b else f x.

End update.

Definition update_register := update physical_register_eqdec.

Definition update_reg (s : state) (m : processor_mode) (Rd : register_number)
  := update_register (reg s) (phy_reg_of_mode m Rd).

Definition reg_content (s : state) (m : processor_mode) (Rn : register_number)
  : word := reg s (phy_reg_of_mode m Rn).

Definition update_memory := update address_eqdec.

(****************************************************************************)
(* Chapter A3 - The ARM Instruction Set *)
(****************************************************************************)

(****************************************************************************)
(* A3.2 The condition field (p. 111) *)
(****************************************************************************)

Definition cond_mask := (*bits[28:31]*) repr 4026531840.
Definition cond (r : status_register) := intval (and r cond_mask).

Definition ConditionPassed (r : status_register) : bool :=
  match cond r with
    | (*0000*) 0 => (* Z set *) set_Z r
    | (*0001*) 1 => (* Z clear *) negb (set_Z r)
    | (*0010*) 2 => (* C set *) set_C r
    | (*0011*) 3 => (* C clear *) negb (set_C r)
    | (*0100*) 4 => (* N set *) set_C r
    | (*0101*) 5 => (* N clear *) negb (set_C r)
    | (*0110*) 6 => (* V set *) set_V r
    | (*0111*) 7 => (* V clear *) negb (set_V r)
    | (*1000*) 8 => (* C set and Z clear *)
      andb (set_C r) (negb (set_Z r))
    | (*1001*) 9 => (* C clear or Z set *)
      orb (negb (set_C r)) (set_Z r)
    | (*1010*) 10 => (* N set and V set, or N clear and V clear (N==V) *)
      eqb (set_N r) (set_V r)
    | (*1011*) 11 => (* N set and V clear, or N clear and V set (N!=V) *)
      negb (eqb (set_N r) (set_V r))
    | (*1100*) 12 => (* Z clear, and either N set and V set,
         or N clear and V clear (Z==0,N==V) *)
      andb (negb (set_Z r)) (eqb (set_N r) (set_V r))
    | (*1101*) 13 => (* Z set, or N set and V clear, or N clear and V set
         (Z==1 or N!=V) *)
      orb (set_Z r) (negb (eqb (set_N r) (set_V r)))
    | _ => true
  end.

(****************************************************************************)
(* A3.3 Branch instructions (p. 113) *)
(****************************************************************************)

Inductive branch_instruction : Type := B | BL | BLX | BX | BXJ.

(****************************************************************************)
(* A3.4 Data-processing instructions (p. 115) *)
(****************************************************************************)

Inductive data_processing_instruction : Type :=
  AND | EOR | SUB | RSB | ADD | ADC | SBC | RSC
| TST | TEQ | CMP | CMN | ORR | MOV | BIC | MVN.

(****************************************************************************)
(* A3.5 Multiply instructions (p. 117) *)
(****************************************************************************)

Inductive multiply_instruction : Type :=
  MLA | MUL | SMLA | SMLAD | SMLAL | SMLALD | SMLAW | SMLSD | SMLSLD | SMMLA
| SMMLS | SMMUL | SMUAD | SMUL | SMULL | SMULW | SMUSD | UMAAL | UMLAL | UMULL.

(****************************************************************************)
(* A3.6 Parallel addition and subtraction instructions (p. 122) *)
(****************************************************************************)

Inductive parallel_addition_instruction_code : Type :=
  ADD16 | ADDSUBX | SUBADDX | SUB16 | ADD8 | SUB8.

Inductive parallel_addition_instruction_prefix : Type :=
  PAS | PAQ | PASH | PAU | PAUQ | PAUH.

Definition parallel_addition_instruction :=
  (parallel_addition_instruction_prefix
    * parallel_addition_instruction_code)%type.

(****************************************************************************)
(* A3.7 Extend instructions (p. 124) *)
(****************************************************************************)

Inductive extend_instruction_code : Type :=
  XTAB16 | XTAB | XTAH | XTB16 | XTB | XTH.

Inductive extend_instruction_prefix : Type := XS | XU.

Definition extend_instruction :=
  (extend_instruction_prefix * extend_instruction_code)%type.

(****************************************************************************)
(* A3.8 Miscellaneous arithmetic instructions (p. 125) *)
(****************************************************************************)

Inductive miscellaneous_arithmetic_instruction : Type :=
  CLZ | USAD8 | USADA8.

(****************************************************************************)
(* A3.9 Other miscellaneous instructions (p. 126) *)
(****************************************************************************)

Inductive other_miscellaneous_instruction : Type :=
  PKHBT | PKHTB | REV | REV16 | REVSH | SEL | SSAT | SSAT16 | USAT | USAT16.

(****************************************************************************)
(* A3.10 Status register access instructions (p. 127) *)
(****************************************************************************)

Inductive status_register_access_instruction : Type :=
  MRS | MSR | CPS | SETEND.

(****************************************************************************)
(* A3.11 Load and Store instructions (p. 129) *)
(****************************************************************************)

Inductive load_and_store_instruction : Type :=
  LDR | LDRB | LDRBT | LDRD | LDREX | LDRH | LDRSB | LDRSH | LDRT
| STR | STRB | STRBT | STRD | STREX | STRH | STRT.

(****************************************************************************)
(* A3.12 Load and Store Multiple instructions (p. 134) *)
(****************************************************************************)

Inductive addressing_mode : Type := IA | IB | DA | DB | FD | FA | ED | EA.

Inductive load_and_store_multiple_instruction : Type := LDM | STM.

(****************************************************************************)
(* A3.13 Semaphore instructions (p. 136) *)
(****************************************************************************)

Inductive semaphore_instruction : Type := SWP | SWPB.

(****************************************************************************)
(* A3.14 Exception-generating instructions (p. 137) *)
(****************************************************************************)

Inductive exception_generating_instruction : Type := BKPT | SWI.

(****************************************************************************)
(* A3.15 Coprocessor instructions (P. 138) *)
(****************************************************************************)

Inductive coprocessor_instruction : Type :=
  CDP | LDC | MCR | MCRR | MRC | MRRC | STC.

(****************************************************************************)
(* A3.16 Extending the instruction set (p. 140) *)
(****************************************************************************)

(****************************************************************************)
(* Chapter A4 - ARM Instructions *)
(****************************************************************************)

Definition result := option state.

Definition Unpredictable := @None state.

(****************************************************************************)
(* A4.1.2 ADC (p. 154) *)
(****************************************************************************)

(*
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
*)

Definition adc (s : state) (S : bool) (Rd Rn : register_number) (so : int)
  : option state :=
  let r := cpsr s in
    match mode r with
      | None => Unpredictable (* p. 52 *)
      | Some m =>
        if ConditionPassed r then
          let reg' := update_reg s m Rd
            (add (add (reg_content s m Rn) so) (Cbit r)) in
          if S then
            match m with
              | usr | sys => Unpredictable
              | exn e =>
                if is_eq Rd 15 then
                  Some (mk_state (spsr s e) (spsr s) reg' (mem s) (exns s))
                else
                  let cpsr' := or r (and Nmask (reg_content s m Rd)) in
                    Some (mk_state (cpsr s) (spsr s) reg' (mem s) (exns s))
            end
          else Some s
        else Some s
    end.
