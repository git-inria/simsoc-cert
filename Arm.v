(**
SimSoC-Cert, a Coq library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.
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

Definition zne (x y : Z) : bool := negb (zeq x y).

Definition neb (x y : bool) : bool := negb (eqb x y).

(* nat_of_Z defined in ZArith, as well as
Zpos_eq_Z_of_nat_o_nat_of_P:
  forall p : positive, Zpos p = Z_of_nat (nat_of_P p)

Zpos_P_of_succ_nat:
  forall n : nat, Zpos (P_of_succ_nat n) = Zsucc (Z_of_nat n)
*)

Definition nat_of_Z (x : Z) : nat :=
  match x with
    | Zpos p => nat_of_P p
    | _ => O
  end.

(* Yet another test *)
Lemma nat_of_Z_ok : forall x : Z, x >= 0 -> Z_of_nat (nat_of_Z x) = x.
Proof.
  destruct x; simpl.
    reflexivity.
    intros _. rewrite Zpos_eq_Z_of_nat_o_nat_of_P. reflexivity.
    compute. intro n; case n; reflexivity.
Qed.


(****************************************************************************)
(* Architecture versions (p. 13) *)
(****************************************************************************)

Inductive version : Type :=
(* All architecture names prior to ARMv4 are now OBSOLETE *)
| ARMv4 | ARMv4T
| ARMv5T | ARMv5TExP (*for legacy reasons only*) | ARMv5TE | ARMv5TEJ
| ARMv6.

(****************************************************************************)
(* Chapter A2 - Programmers’ Model (p. 39) *)
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

Coercion intval : word >-> Z.

Definition two : word := repr 2.
Definition w31 : word := repr 31.
Definition maxu : word := repr max_unsigned.
Definition max : word := repr max_signed.
Definition min : word := repr min_signed.

Definition word_of_bool (b : bool) : word := if b then one else zero.

(* mask made of bit [n] *)

Definition mask (n : nat) : word := repr (two_power_nat n).

(* mask made of the bits from bit [n] to bit [n+k] *)

Fixpoint masks_aux (n k : nat) : Z :=
  match k with
    | O => two_power_nat n
    | S k' => two_power_nat n + masks_aux (S n) k'
  end.

(* mask made of the bits from bit [n] to bit [n+(p-n)] *)

Definition masks (n p : nat) : word := repr (masks_aux n (p-n)).

(* test to zero *)

Definition eq_0 (w : word) : word := word_of_bool (zeq 0 w).
Definition ne_0 (w : word) : word := word_of_bool (zne 0 w).

(* bit(s) of a word *)

Definition subword (k l : nat) (w : word) : word := and (masks k l) w.
Definition subword_val (k l : nat) (w : word) : Z := intval (subword k l w).

Definition bit (k : nat) (w : word) : word := and (mask k) w.
Notation get := bit.
Definition is_set (k : nat) (w : word) : bool := zne 0 (bit k w).
Definition set (k : nat) (w : word) : word := or (mask k) w.
Definition clear (k : nat) (w : word) : word := and (not (mask k)) w.
Definition update (k : nat) (w x : word) : word :=
  if zeq 0 x then clear k w else set k w.

Definition is_signed (w : word) : bool := zne 0 (bit 31 w).

(*FIXME: replace bits by generalizing in Integers the type int by
taking wordsize as a parameter?*)

Section bitvec.

Variable n : nat.

Let modulus := two_power_nat n.

Record bitvec : Type := build_bitvec {
  bitvec_val :> Z;
  bitvec_prf : 0 <= bitvec_val < modulus
}.

Lemma bitvec_in_range: forall x, 0 <= Zmod x modulus < modulus.

Proof.
intro x. exact (Z_mod_lt x modulus (two_power_nat_pos n)).
Qed.

Definition mk_bitvec (x : Z) : bitvec := build_bitvec (bitvec_in_range x).

Lemma bitvec_eqdec : forall b1 b2 : bitvec, {b1=b2}+{~b1=b2}.

Proof.
intros [v1 p1] [v2 p2]. case (zeq v1 v2); intro.
left. subst. rewrite (proof_irrelevance _ p1 p2). auto.
right. intro h. inversion h. contradiction.
Qed.

End bitvec.

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

Definition reg_num := bitvec 4.
Definition mk_reg_num := mk_bitvec 4.

Definition is_eq (Rd : reg_num) (x : Z) : bool := zeq (bitvec_val Rd) x.

(*FIXME: can be improved by using build_bitvec instead of mk_bitvec
since [unsigned (and w (masks k (k+3)))] is always smaller than
[two_power_nat 4]*)
Definition reg_num_of (k : nat) (w : word) : reg_num :=
  mk_reg_num (unsigned (and w (masks k (k+3)))).

Inductive register : Type :=
| R (k : reg_num)
| R_svc (k : Z) (h : 13 <= k <= 14)
| R_abt (k : Z) (h : 13 <= k <= 14)
| R_und (k : Z) (h : 13 <= k <= 14)
| R_irq (k : Z) (h : 13 <= k <= 14)
| R_fiq (k : Z) (h : 8 <= k <= 14).

Lemma register_eqdec : forall x y : register, {x=y}+{~x=y}.

Proof.
destruct x; destruct y; intros; try (right; discriminate).
destruct (bitvec_eqdec k k0). subst. auto.
right. intro h. inversion h. contradiction.
destruct (zeq k k0). subst. rewrite (proof_irrelevance _ h0 h). auto.
right. intro p. inversion p. contradiction.
destruct (zeq k k0). subst. rewrite (proof_irrelevance _ h0 h). auto.
right. intro p. inversion p. contradiction.
destruct (zeq k k0). subst. rewrite (proof_irrelevance _ h0 h). auto.
right. intro p. inversion p. contradiction.
destruct (zeq k k0). subst. rewrite (proof_irrelevance _ h0 h). auto.
right. intro p. inversion p. contradiction.
destruct (zeq k k0). subst. rewrite (proof_irrelevance _ h0 h). auto.
right. intro p. inversion p. contradiction.
Qed.

Definition reg_of_exn_mode (m : processor_exception_mode)
  (k : reg_num) : register :=
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

Definition reg_of_mode (m : processor_mode) (k : reg_num)
  : register :=
  match m with
    | usr | sys => R k
    | exn e => reg_of_exn_mode e k
  end.

(****************************************************************************)
(* A2.5 Program status registers (p. 49) *)
(****************************************************************************)

(* Condition code flags (p. 49) *)

Definition Nbit := 31%nat.
Definition Zbit := 30%nat.
Definition Cbit := 29%nat.
Definition Vbit := 28%nat.

(* The Q flag (p. 51) *)

Definition Qbit := 27%nat.

(* The GE bits (p. 51) *)

Definition GEbits w := subword 16 19 w.

(* The E bit (p. 51) *)

Definition Ebit := 9%nat.

(* The interrupt disable bits (p. 52) *)

Definition Abit := 8%nat.
Definition Ibit := 7%nat.
Definition Fbit := 6%nat.

(* Mode bits (p. 52) *)

Definition Mbits w := subword_val 0 4 w.

Definition mode (w : word) : option processor_mode :=
  match Mbits w with
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
  cpsr : word; (* Current program status register *)
  spsr : processor_exception_mode -> word;
    (* Saved program status registers *)
  reg : register -> word;
  mem : address -> word;
  exns : list exception (* Raised exceptions *)
}.

(*FIXME: does not work :-(
Notation "s .cpsr" := (cpsr s) (at level 2, left associativity).
Notation "s .spsr" := (spsr s) (at level 2, left associativity).
Notation "s .reg" := (reg s) (at level 2, left associativity).
Notation "s .mem" := (mem s) (at level 2, left associativity).
Notation "s .exns" := (exns s) (at level 2, left associativity).*)

Definition reg_content s m k := reg s (reg_of_mode m k).

Definition set_cpsr s w := mk_state w (spsr s) (reg s) (mem s) (exns s).
Definition set_spsr s x := mk_state (cpsr s) x (reg s) (mem s) (exns s).
Definition set_reg s x :=  mk_state (cpsr s) (spsr s) x (mem s) (exns s).
Definition set_mem s x :=  mk_state (cpsr s) (spsr s) (reg s) x (exns s).
Definition set_exns s x :=  mk_state (cpsr s) (spsr s) (reg s) (mem s) x.

Definition set_cpsr_or s w := set_cpsr s (or (cpsr s) w).

Definition add_exn s e := set_exns s (insert e (exns s)).

Section update_map.

Variables (A : Type) (eqdec : forall x y : A, {x=y}+{~x=y}) (B : Type).

Definition update_map (a : A) (b : B) (f : A -> B) : A -> B :=
  fun x => if eqdec x a then b else f x.

End update_map.

Definition update_map_spsr s m w :=
  update_map processor_exception_mode_eqdec m w (spsr s).
Definition update_map_reg s m k w :=
  update_map register_eqdec (reg_of_mode m k) w (reg s).
Definition update_map_mem s a w :=
  update_map address_eqdec a w (mem s).

Definition update_spsr s m w := set_spsr s (update_map_spsr s m w).
Definition update_reg s m k w := set_reg s (update_map_reg s m k w).
Definition update_mem s a w := set_mem s (update_map_mem s a w).

(****************************************************************************)
(* Chapter A5 - ARM Addressing Modes (p. 441) *)
(****************************************************************************)

(****************************************************************************)
(* A5.1 Addressing Mode 1 - Data-processing operands (p. 442) *)
(****************************************************************************)

Inductive shifter : Type := LSL | LSR | ASR | ROR.

Inductive shifter_value : Type :=
| ValImm (shift_imm : word)
| ValReg (Rs : reg_num).

Inductive shifter_operand : Type :=
| Imm (rotate_imm immed_8 : word)
| Shift (Rm : reg_num) (s : shifter) (v : shifter_value)
| RRX (Rm : reg_num).

(* A5.1.1 Encoding (p. 443) *)

Definition decode_shifter (w : word) : shifter :=
  match subword_val 5 6 w with
    | (*00*) 0 => LSL
    | (*01*) 1 => LSR
    | (*10*) 2 => ASR
    | (*11*) _ => ROR
  end.

Definition decode_shifter_operand (w : word) (x z : bool) : shifter_operand :=
  if x then Imm (subword 8 11 w) (subword 0 7 w)
  else Shift (reg_num_of 0 w) (decode_shifter w)
    (if z then ValImm (subword 7 11 w) else ValReg (reg_num_of 8 w)).

(* Logical_Shift_Left (p. 1129) *)
(* Performs a left shift, inserting zeros in the vacated bit positions
on the right. *)
Definition Logical_Shift_Left := shl. (*FIXME?*)

(* Logical_Shift_Right (p. 1129) *)
(* Performs a right shift, inserting zeros in the vacated bit
positions on the left. *)
Definition Logical_Shift_Right := shru. (*FIXME?*)

(* Arithmetic_Shift_Right (p. 1121) *)
(* Performs a right shift, repeatedly inserting the original left-most
bit (the sign bit) in the vacated bit positions on the left. *)
Definition Arithmetic_Shift_Right := shr. (*FIXME?*)

(* Rotate_Right (p. 1132) *)
(* Performs a right rotate, where each bit that is shifted off the
right is inserted on the left. *)
Definition Rotate_Right := ror. (*FIXME?*)

(* A5.1.3 Data-processing operands - Immediate (p. 446) *)
(*
shifter_operand = immed_8 Rotate_Right (rotate_imm * 2)
if rotate_imm == 0 then
  shifter_carry_out = C flag
else /* rotate_imm != 0 */
  shifter_carry_out = shifter_operand[31]
*)
Definition so_imm (i : word) (rotate_imm immed_8 : word) : word * bool :=
  let v := Rotate_Right immed_8 (mul two rotate_imm) in
  let c := if zeq rotate_imm 0 then is_set Cbit i else is_set 31 v in
  (v, c).

(* A5.1.4 Data-processing operands - Register (p. 448) *)
(*
shifter_operand = Rm
shifter_carry_out = C Flag
*)
Definition so_reg (s : state) (m : processor_mode) (i : word) (Rm : reg_num)
  : word * bool := (reg_content s m Rm, is_set Cbit i).

(* A5.1.5 Data-processing operands - Logical shift left by immediate (p. 449) *)
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

(* A5.1.6 Data-processing operands - Logical shift left by register (p. 450) *)
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
  let Rs7 := subword 0 7 (reg_content s m Rs) in
  if zeq Rs7 0 then (Rm, is_set Cbit i)
  else match Zcompare Rs7 32 with
         | Lt => (Logical_Shift_Left Rm Rs7, is_set (nat_of_Z (32 - Rs7)) Rm)
         | Eq => (zero, is_set 0 Rm)
         | Gt => (zero, false)
       end.

(* A5.1.7 Data-processing operands - Logical shift right by immediate (p. 451) *)
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
  if zeq shift_imm 0 then (zero, is_set 31 Rm)
  else (Logical_Shift_Right Rm shift_imm,
    is_set (pred (nat_of_Z shift_imm)) Rm).

(* A5.1.8 Data-processing operands - Logical shift right by register (p. 452) *)
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
  let Rs7 := subword 0 7 (reg_content s m Rs) in
  if zeq Rs7 0 then (Rm, is_set Cbit i)
  else match Zcompare Rs7 32 with
         | Lt => (Logical_Shift_Right Rm Rs7, is_set (pred (nat_of_Z Rs7)) Rm)
         | Eq => (zero, is_set 31 Rm)
         | Gt => (zero, false)
       end.

(* A5.1.9 Data-processing operands - Arithmetic shift right by immediate (p. 453) *)
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
    if is_set 31 Rm then (maxu, true) else (zero, false)
  else (Arithmetic_Shift_Right Rm shift_imm,
    is_set (pred (nat_of_Z shift_imm)) Rm).

(* A5.1.10 Data-processing operands - Arithmetic shift right by register (p. 454) *)
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
  let Rs7 := subword 0 7 (reg_content s m Rs) in
  if zeq Rs7 0 then (Rm, is_set Cbit i)
  else match Zcompare Rs7 32 with
         | Lt => (Arithmetic_Shift_Right Rm Rs7,
           is_set (pred (nat_of_Z Rs7)) Rm)
         | _ => if is_set 31 Rm then (maxu, true) else (zero, false)
       end.

(* A5.1.11 Data-processing operands - Rotate right by immediate (p. 455) *)
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
    (or (Logical_Shift_Left (get Cbit i) w31) (Logical_Shift_Right Rm one),
      is_set 0 Rm)
  else (Rotate_Right Rm shift_imm, is_set (pred (nat_of_Z shift_imm)) Rm).

(* A5.1.12 Data-processing operands - Rotate right by register (p. 456) *)
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
  let Rs7 := subword 0 7 Rs in
  if zeq Rs7 0 then (Rm, is_set Cbit i)
  else let Rs4 := subword 0 4 Rs in
    if zeq Rs4 0 then (Rm, is_set 31 Rm)
    else (Rotate_Right Rm Rs4, is_set (pred (nat_of_Z Rs4)) Rm).

(* A5.1.13 Data-processing operands - Rotate right with extend (p. 457) *)
(*
shifter_operand = (C Flag Logical_Shift_Left 31) OR (Rm Logical_Shift_Right 1)
shifter_carry_out = Rm[0]
*)
Definition so_RRX (s : state) (m : processor_mode) (i : word) (Rm : reg_num)
  : word * bool :=
  let Rm := reg_content s m Rm in
    (or (Logical_Shift_Left (get Cbit i) w31) (Logical_Shift_Right Rm one),
      is_set 0 Rm).

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

(****************************************************************************)
(* Chapter A3 - The ARM Instruction Set (p. 109) *)
(****************************************************************************)

(****************************************************************************)
(* A3.2 The condition field (p. 111) *)
(****************************************************************************)

Definition ConditionPassed (w : word) : bool :=
  match subword_val 28 31 w with
    | (*0000*) 0 => (* Z set *) is_set Zbit w
    | (*0001*) 1 => (* Z clear *) negb (is_set Zbit w)
    | (*0010*) 2 => (* C set *) is_set Cbit w
    | (*0011*) 3 => (* C clear *) negb (is_set Cbit w)
    | (*0100*) 4 => (* N set *) is_set Cbit w
    | (*0101*) 5 => (* N clear *) negb (is_set Cbit w)
    | (*0110*) 6 => (* V set *) is_set Vbit w
    | (*0111*) 7 => (* V clear *) negb (is_set Vbit w)
    | (*1000*) 8 => (* C set and Z clear *)
      andb (is_set Cbit w) (negb (is_set Zbit w))
    | (*1001*) 9 => (* C clear or Z set *)
      orb (negb (is_set Cbit w)) (is_set Zbit w)
    | (*1010*) 10 => (* N set and V set, or N clear and V clear (N==V) *)
      eqb (is_set Nbit w) (is_set Vbit w)
    | (*1011*) 11 => (* N set and V clear, or N clear and V set (N!=V) *)
      negb (eqb (is_set Nbit w) (is_set Vbit w))
    | (*1100*) 12 => (* Z clear, and either N set and V set,
         or N clear and V clear (Z==0,N==V) *)
      andb (negb (is_set Zbit w)) (eqb (is_set Nbit w) (is_set Vbit w))
    | (*1101*) 13 => (* Z set, or N set and V clear, or N clear and V set
         (Z==1 or N!=V) *)
      orb (is_set Zbit w) (negb (eqb (is_set Nbit w) (is_set Vbit w)))
    | _ => true
  end.

(****************************************************************************)
(* Chapter A4 - ARM Instructions (p. 151) *)
(****************************************************************************)

Inductive instruction : Type :=
| ADC (S : bool) (Rd Rn : reg_num) (so : shifter_operand).

(****************************************************************************)
(* Instruction decoding *)
(****************************************************************************)

(*FIXME: should be replaced by option type when all instructions
will be formalized*)
Inductive decoding_result : Type :=
| Inst (i : instruction)
| Undefined
| Todo.

Section clist.

Variables (A : Type) (a : A).

Fixpoint clist (k : nat) : list A :=
  match k with
    | O => nil
    | S k' => a :: clist k'
  end.

End clist.

Fixpoint bools_of_positive (p : positive) (acc : list bool) : list bool :=
  match p with
    | xI p' => bools_of_positive p' (false :: acc)
    | xO p' => bools_of_positive p' (true :: acc)
    | xH => true :: acc
  end.

Definition bools_of_word (w : word) : list bool :=
  match unsigned w with
    | Zpos p => bools_of_positive p nil
    | _ => clist false wordsize
  end.

Section decode.

Local Notation "0" := false.
Local Notation "1" := true.
Local Infix "'" := cons (at level 60, right associativity).

Definition decode (w : word) : decoding_result :=
  match bools_of_word w with
   (* A4.1.2 ADC (p. 154) *)
   (*31 30 29 28 27 26 25 24 23 22 21 20 19 18 17 16 15 14 13 12 10 09 08 07 06 05 04 03 02 01*)
    | _ '_ '_ '_ '0 '0 'i '0 '1 '0 '1 's '_ '_ '_ '_ '_ '_ '_ '_ '_ '_ '_ 'x '_ '_ 'y '_ '_ '_ '_ =>
      (*FIXME: only if [negb (negb I && X && Y)] *)
      Inst (ADC s (reg_num_of 12 w) (reg_num_of 16 w) (decode_shifter_operand w i y))
    | _ => Todo
  end.

End decode.

(****************************************************************************)
(* Instruction semantics *)
(****************************************************************************)

Definition result := option state.

Definition Unpredictable := @None state.

(* CurrentModeHasSPSR (p. 1125) *)

Definition CurrentModeHasSPSR (m : processor_mode) : bool :=
  match m with
    | usr | sys => false
    | _ => true
  end.

(* CarryFrom (p. 1124) *)

Definition CarryFrom_add2 (x y : word) : word :=
  word_of_bool (zlt max_unsigned (unsigned x + unsigned y)).

Definition CarryFrom_add3 (x y z : word) : word :=
  word_of_bool (zlt max_unsigned (unsigned x + unsigned y + unsigned z)).

(* OverflowFrom (p. 1131) *)

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

Definition adc (S : bool) (Rd Rn : reg_num) (so : word) (s : state)
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
                let s := update_reg s m Rd v in
                if is_eq Rd 15 then Some (set_cpsr s (spsr s e))
                else Some (set_cpsr_or s
                  (update Nbit (bit 31 v)
                    (update Zbit (ne_0 v)
                      (update Cbit (CarryFrom_add3 Rn so c)
                        (update Vbit (OverflowFrom_add3 Rn so c) r)))))
            end
          else let Rn := reg_content s m Rn in
            let c := get Cbit r in
            let v := add (add Rn so) c in
              Some (update_reg s m Rd v)
        else Some s
    end.

End Arm.
