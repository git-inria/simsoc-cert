(**
SimSoC-Cert, a Coq library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

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

Definition neb (x y : bool) : bool := negb (eqb x y).

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

Definition store_pc_offset (v : store_pc_offset_value) : int :=
  match v with
    | O8 => repr 8
    | O12 => repr 12
  end.
 
(* A2.6.5 Abort models *)

Inductive abort_model : Type := Restored | Updated.

(* All parameters gathered *)
(*FIXME: to be completed*)
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

Notation word := int.

(* mask made of bit [n] *)

Definition mask (n : nat) : word := repr (two_power_nat n).

Definition mask0 := mask 0. Definition mask1 := mask 1.
Definition mask2 := mask 2. Definition mask3 := mask 3.
Definition mask4 := mask 4. Definition mask5 := mask 5.
Definition mask6 := mask 6. Definition mask7 := mask 7.
Definition mask8 := mask 8. Definition mask9 := mask 9.
Definition mask10 := mask 10. Definition mask11 := mask 11.
Definition mask12 := mask 12. Definition mask13 := mask 13.
Definition mask14 := mask 14. Definition mask15 := mask 15.
Definition mask16 := mask 16. Definition mask17 := mask 17.
Definition mask18 := mask 18. Definition mask19 := mask 19.
Definition mask20 := mask 20. Definition mask21 := mask 21.
Definition mask22 := mask 22. Definition mask23 := mask 23.
Definition mask24 := mask 24. Definition mask25 := mask 25.
Definition mask26 := mask 26. Definition mask27 := mask 27.
Definition mask28 := mask 28. Definition mask29 := mask 29.
Definition mask30 := mask 30. Definition mask31 := mask 31.

(* mask made of the bits from bit [n] to bit [n+k] *)

Fixpoint masks_aux (n k : nat) : Z :=
  match k with
    | O => two_power_nat n
    | S k' => two_power_nat n + masks_aux (S n) k'
  end.

(* mask made of the bits from bit [n] to bit [n+(p-n)] *)

Definition masks (n p : nat) : word := repr (masks_aux n (p-n)).

(* test to zero *)

Definition word_of_bool (b : bool) : word := if b then one else zero.
Definition is_zero (w : word) : bool := zeq (intval w) 0.
Definition word_is_zero (w : word) : word := word_of_bool (is_zero w).
Definition is_not_zero (w : word) : bool := negb (is_zero w).
Definition word_is_not_zero (w : word) : word := word_of_bool (is_not_zero w).

(* bit of a word *)

Definition bit (k : nat) (w : word) : word := and (mask k) w.
Notation get := bit.
Definition is_set (k : nat) (w : word) : bool := is_not_zero (bit k w).
Definition set (k : nat) (w : word) : word := or (mask k) w.
Definition clear (k : nat) (w : word) : word := and (not (mask k)) w.
Definition update (k : nat) (w x : word) : word :=
  if is_not_zero x then set k w else clear k w.

Definition is_signed (w : word) : bool := is_not_zero (bit 31 w).

(*REMOVE?Fixpoint ors (ws : list word) : word :=
  match ws with
    | nil => zero
    | w :: ws' => or w (ors ws')
  end.*)

(*FIXME: replace bits by generalizing in Integers the type int by
taking wordsize as a parameter?*)
Record bitvec (n : nat) : Type := mk_bitvec {
  bitvec_val :> Z;
  bitvec_prf : 0 <= bitvec_val < two_power_nat n
}.

Lemma bitvec_eqdec : forall n (b1 b2 : bitvec n), {b1=b2}+{~b1=b2}.

Proof.
intros n [v1 p1] [v2 p2]. case (zeq v1 v2); intro.
left. subst. rewrite (proof_irrelevance _ p1 p2). auto.
right. intro h. inversion h. contradiction.
Qed.

(*FIXME: do we need to define types for bytes and halfwords?*)
Definition halfword := bitvec 16.
Definition byte := bitvec 8.

(****************************************************************************)
(* A2.2 Processor modes (p. 410) *)
(****************************************************************************)

Module Arm (C : CONFIG).

Inductive processor_exception_mode : Type := fiq | irq | svc | abt | und.

Lemma processor_exception_mode_eqdec :
  forall x y : processor_exception_mode, {x=y}+{~x=y}.

Proof. decide equality. Qed.

Inductive processor_mode : Type :=
  usr | sys | exn (m : processor_exception_mode).

(****************************************************************************)
(* A2.3 Registers (p. 42) *)
(* A2.4 General-purpose registers (p. 44) *)
(****************************************************************************)

Definition register_number := bitvec 4.

Definition is_eq (Rd : register_number) (x : Z) : bool := zeq (bitvec_val Rd) x.

Inductive physical_register : Type :=
| R (r : register_number)
| R_svc (v : Z) (h : 13 <= v <= 14)
| R_abt (v : Z) (h : 13 <= v <= 14)
| R_und (v : Z) (h : 13 <= v <= 14)
| R_irq (v : Z) (h : 13 <= v <= 14)
| R_fiq (v : Z) (h : 8 <= v <= 14).

Lemma physical_register_eqdec : forall x y : physical_register, {x=y}+{~x=y}.

Proof.
destruct x; destruct y; intros; try (right; discriminate).
destruct (bitvec_eqdec r r0). subst. auto.
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

Definition Nbit := 31%nat.
Definition Zbit := 30%nat.
Definition Cbit := 29%nat.
Definition Vbit := 28%nat.

(* The Q flag (p. 51) *)

Definition Qbit := 27%nat.

(* The GE bits (p. 51) *)

Definition GEmask := masks 16 19.
Definition GEbits r := and r GEmask.

(* The E bit (p. 51) *)

Definition Ebit := 9%nat.

(* The interrupt disable bits (p. 52) *)

Definition Abit := 8%nat.
Definition Ibit := 7%nat.
Definition Fbit := 6%nat.

(* Mode bits (p. 52) *)

Definition Mmask := masks 0 4.
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

Definition Tbit := 5%nat.
Definition Jbit := 24%nat.

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

Fixpoint insert (e : exception) (l : list exception) : list exception :=
  match l with
    | nil => e :: nil
    | e' :: l' => if zlt (priority e) (priority e') then e :: l
      else e' :: insert e l'
  end.

(****************************************************************************)
(* A2.7 Endian support (p. 68) *)
(****************************************************************************)

Definition address := bitvec 30.

Definition address_eqdec := @bitvec_eqdec 30.

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
  reg : physical_register -> word;
  mem : address -> word;
  exns : list exception (* Raised exceptions *)
}.

(*FIXME: does not work :-(
Notation "s .cpsr" := (cpsr s) (at level 2, left associativity).
Notation "s .spsr" := (spsr s) (at level 2, left associativity).
Notation "s .reg" := (reg s) (at level 2, left associativity).
Notation "s .mem" := (mem s) (at level 2, left associativity).
Notation "s .exns" := (exns s) (at level 2, left associativity).*)

Definition reg_content (s : state) (m : processor_mode) (Rn : register_number)
  : word := reg s (phy_reg_of_mode m Rn).

Section update_map.

Variables (A : Type) (eqdec : forall x y : A, {x=y}+{~x=y}) (B : Type).

Definition update_map (a : A) (b : B) (f : A -> B) : A -> B :=
  fun x => if eqdec x a then b else f x.

End update_map.

Definition update_spsr (m : processor_exception_mode) (w : word) (s : state)
  : processor_exception_mode -> word
  := update_map processor_exception_mode_eqdec m w (spsr s).

Definition update_reg (m : processor_mode) (Rd : register_number) (w : word)
  (s : state) : physical_register -> word :=
  update_map physical_register_eqdec (phy_reg_of_mode m Rd) w (reg s).

Definition update_mem (a : address) (w : word) (s : state) : address -> word :=
  update_map address_eqdec a w (mem s).

Definition set_cpsr (s : state) (w : word) : state :=
  mk_state w (spsr s) (reg s) (mem s) (exns s).

Definition update_cpsr (w : word) (s : state) : state :=
  set_cpsr s (or (cpsr s) w).

Definition set_spsr (s : state) (m : processor_exception_mode) (w : word)
  : state := mk_state (cpsr s) (update_spsr m w s) (reg s) (mem s) (exns s).

Definition set_reg (s : state) (m : processor_mode) (Rd : register_number)
  (w : word) : state :=
  mk_state (cpsr s) (spsr s) (update_reg m Rd w s) (mem s) (exns s).

Definition set_mem (s : state) (a : address) (w : word) : state :=
  mk_state (cpsr s) (spsr s) (reg s) (update_mem a w s) (exns s).

Definition add_exn (s : state) (e : exception) : state :=
  mk_state (cpsr s) (spsr s) (reg s) (mem s) (insert e (exns s)).

(****************************************************************************)
(* Chapter A3 - The ARM Instruction Set *)
(****************************************************************************)

(****************************************************************************)
(* A3.2 The condition field (p. 111) *)
(****************************************************************************)

Definition cond_mask := masks 28 3. (*bits[28:31]*)
Definition cond (r : status_register) := intval (and r cond_mask).

Definition ConditionPassed (r : status_register) : bool :=
  match cond r with
    | (*0000*) 0 => (* Z set *) is_set Zbit r
    | (*0001*) 1 => (* Z clear *) negb (is_set Zbit r)
    | (*0010*) 2 => (* C set *) is_set Cbit r
    | (*0011*) 3 => (* C clear *) negb (is_set Cbit r)
    | (*0100*) 4 => (* N set *) is_set Cbit r
    | (*0101*) 5 => (* N clear *) negb (is_set Cbit r)
    | (*0110*) 6 => (* V set *) is_set Vbit r
    | (*0111*) 7 => (* V clear *) negb (is_set Vbit r)
    | (*1000*) 8 => (* C set and Z clear *)
      andb (is_set Cbit r) (negb (is_set Zbit r))
    | (*1001*) 9 => (* C clear or Z set *)
      orb (negb (is_set Cbit r)) (is_set Zbit r)
    | (*1010*) 10 => (* N set and V set, or N clear and V clear (N==V) *)
      eqb (is_set Nbit r) (is_set Vbit r)
    | (*1011*) 11 => (* N set and V clear, or N clear and V set (N!=V) *)
      negb (eqb (is_set Nbit r) (is_set Vbit r))
    | (*1100*) 12 => (* Z clear, and either N set and V set,
         or N clear and V clear (Z==0,N==V) *)
      andb (negb (is_set Zbit r)) (eqb (is_set Nbit r) (is_set Vbit r))
    | (*1101*) 13 => (* Z set, or N set and V clear, or N clear and V set
         (Z==1 or N!=V) *)
      orb (is_set Zbit r) (negb (eqb (is_set Nbit r) (is_set Vbit r)))
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

(* CurrentModeHasSPSR p. 1125 *)

Definition CurrentModeHasSPSR (m : processor_mode) : bool :=
  match m with
    | usr | sys => false
    | _ => true
  end.

(* CarryFrom p. 1124 *)

Definition CarryFrom_add2 (x y : word) : word :=
  word_of_bool (zlt max_unsigned (unsigned x + unsigned y)).

Definition CarryFrom_add3 (x y z : word) : word :=
  word_of_bool (zlt max_unsigned (unsigned x + unsigned y + unsigned z)).

(* OverflowFrom p. 1131 *)

Definition OverflowFrom_add2 (x y : word) : word :=
  word_of_bool (zlt max_signed (signed x + signed y)).

(*FIXME: use this more efficient definition given p. 1131?*)
Definition OverflowFrom_add2' (x y : word) (r : word) :=
  let sx := is_signed x in (eqb sx (is_signed y)) && (neb sx (is_signed r)).

Definition OverflowFrom_add3 (x y z : word) : word :=
  word_of_bool (zlt max_signed (signed x + signed y + signed z)).

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

Definition adc (S : bool) (Rd Rn : register_number) (so : int) (s : state)
  : option state :=
  let r := cpsr s in
    match mode r with
      | None => Unpredictable (* p. 52 *)
      | Some m =>
        if ConditionPassed r then
          if S then
            match m with
              | usr | sys => Unpredictable
              | exn e =>
                let Rn := reg_content s m Rn in
                let c := get Cbit r in
                let v := add (add Rn so) c in
                let s := set_reg s m Rd v in
                if is_eq Rd 15 then Some (set_cpsr s (spsr s e))
                else Some (update_cpsr s
                  (update Nbit (bit 31 v)
                    (update Zbit (word_is_not_zero v)
                      (update Cbit (CarryFrom_add3 Rn so c)
                        (update Vbit (OverflowFrom_add3 Rn so c) r))))))
            end
            else let Rn := reg_content s m Rn in
              let c := get Cbit r in
              let v := add (add Rn so) c in
                Some (set_reg s m Rd v)
        else Some s
    end.
