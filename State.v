(**
SimSoC-Cert, a Coq library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

ARM processor state.
*)

Set Implicit Arguments.

Require Import Bitvec.
Require Import ZArith.
Require Import Coqlib.
Require Import Util.
Require Import Integers. Import Int.

Open Scope Z_scope.

(****************************************************************************)
(** A2.1 Data types (p. 39) *)
(****************************************************************************)

Definition byte := bitvec 8.
Definition halfword := bitvec 16.

(****************************************************************************)
(** A2.2 Processor modes (p. 41) *)
(****************************************************************************)

Inductive processor_exception_mode : Type := fiq | irq | svc | abt | und.

Lemma processor_exception_mode_eqdec :
  forall x y : processor_exception_mode, {x=y}+{~x=y}.

Proof. decide equality. Qed.

Inductive processor_mode : Type :=
  usr | sys | exn (m : processor_exception_mode).

(****************************************************************************)
(** A2.3 Registers (p. 42) & A2.4 General-purpose registers (p. 44) *)
(****************************************************************************)

Definition reg_num := bitvec 4.
Definition mk_reg_num := mk_bitvec 4.

Definition PC := mk_reg_num 15.
Definition LR := mk_reg_num 14.

(*FIXME: can be improved by using build_bitvec instead of mk_bitvec
since [unsigned (and w (masks k (k+3)))] is always smaller than
[two_power_nat 4]*)
Definition reg_num_of_word (k : nat) (w : word) : reg_num :=
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

Definition reg_of_mode (m : processor_mode) (k : reg_num) : register :=
  match m with
    | usr | sys => R k
    | exn e => reg_of_exn_mode e k
  end.

(****************************************************************************)
(** A2.5 Program status registers (p. 49) *)
(****************************************************************************)

(* Condition code flags (p. 49) *)

Definition Nbit := 31%nat.
Definition Zbit := 30%nat.
Definition Cbit := 29%nat.
Definition Vbit := 28%nat.

(* The Q flag (p. 51) *)

Definition Qbit := 27%nat.

(* The GE bits (p. 51) *)

Definition GEbits := bits_val 16 19.

(* The E bit (p. 51) *)

Definition Ebit := 9%nat.

(* The interrupt disable bits (p. 52) *)

Definition Abit := 8%nat.
Definition Ibit := 7%nat.
Definition Fbit := 6%nat.

(* Mode bits (p. 52) *)

Definition Mbits := bits_val 0 4.

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

Inductive instruction_set : Type := ARM | Thumb | Jazelle.

Definition inst_set (w : word) : option instruction_set :=
  match is_set Jbit w, is_set Tbit w with
    | false, false => Some ARM
    | false, true => Some Thumb
    | true, false => Some Jazelle
    | true, true => None
  end.

(****************************************************************************)
(** A2.6 Exceptions (p. 54) *)
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
(** A2.7 Endian support (p. 68) *)
(****************************************************************************)

Definition address := bitvec 30.

Definition address_eqdec := @bitvec_eqdec 30.

(*FIXME: can be improved by using build_bitvec instead of mk_bitvec
since [bits_val 2 31 w] is always smaller than [two_power_nat 30]*)
Definition address_of_word (w : word) : address :=
  mk_bitvec 30 (bits_val 2 31 w).

(****************************************************************************)
(** A2.8 Unaligned access support (p. 76) *)
(****************************************************************************)

(****************************************************************************)
(** A2.9 Unaligned access support (p. 76) *)
(****************************************************************************)

(****************************************************************************)
(** A2.10 The Jazelle Extension *)
(****************************************************************************)

(****************************************************************************)
(** A2.11 Saturated integer arithmetic *)
(****************************************************************************)

(****************************************************************************)
(** ARM state *)
(****************************************************************************)

Record state : Type := mk_state {
  (* Current program status register *)
  cpsr : word;
  (* Saved program status registers *)
  spsr : processor_exception_mode -> word;
  (* Registers *)
  reg : register -> word;
  (* Memory *)
  mem : address -> word;
  (* Raised exceptions *)
  exns : list exception
}.

(*FIXME: does not work :-(
Notation "s .cpsr" := (cpsr s) (at level 2, left associativity).
Notation "s .spsr" := (spsr s) (at level 2, left associativity).
Notation "s .reg" := (reg s) (at level 2, left associativity).
Notation "s .mem" := (mem s) (at level 2, left associativity).
Notation "s .exns" := (exns s) (at level 2, left associativity).*)

Definition reg_content s m k := reg s (reg_of_mode m k).

Definition set_cpsr s x := mk_state x (spsr s) (reg s) (mem s) (exns s).
Definition set_spsr s x := mk_state (cpsr s) x (reg s) (mem s) (exns s).
Definition set_reg s x := mk_state (cpsr s) (spsr s) x (mem s) (exns s).
Definition set_mem s x := mk_state (cpsr s) (spsr s) (reg s) x (exns s).
Definition set_exns s x := mk_state (cpsr s) (spsr s) (reg s) (mem s) x.

Section update_map.

Variables (A : Type) (eqdec : forall x y : A, {x=y}+{~x=y}) (B : Type).

Definition update_map (a : A) (b : B) (f : A -> B) : A -> B :=
  fun x => if eqdec x a then b else f x.

End update_map.

Definition update_map_spsr m w s :=
  update_map processor_exception_mode_eqdec m w (spsr s).
Definition update_map_reg m k w s :=
  update_map register_eqdec (reg_of_mode m k) w (reg s).
Definition update_map_mem a w s :=
  update_map address_eqdec a w (mem s).

Definition update_cpsr w s := set_cpsr s w.
Definition update_cpsr_or w s := set_cpsr s (or (cpsr s) w).
Definition update_spsr m w s := set_spsr s (update_map_spsr m w s).
Definition update_reg m k w s := set_reg s (update_map_reg m k w s).
Definition update_mem a w s := set_mem s (update_map_mem a w s).
Definition add_exn e s := set_exns s (insert e (exns s)).

(****************************************************************************)
(** Executing an instruction generates either:
- [None] to represent UNPREDICTABLE
- [Some (b,s)] where:
-- [b] is a boolean indicating whether the PC needs to be incremented,
-- [s] is the new state. *)
(****************************************************************************)

Definition result := option (bool * state).

(****************************************************************************)
(** Current instruction address
cf. A2.4.3 Register 15 and the program counter,
Reading the program counter (p. 47) *)
(****************************************************************************)

Definition cur_inst_address (s : state) (m : processor_mode) : word :=
  sub (reg_content s m PC) w8.

(****************************************************************************)
(** Next ARM instruction address
cf. A2.7.1 Address space (p. 70) *)
(****************************************************************************)

Definition next_inst_address (s : state) (m : processor_mode) : word :=
  (* [add (cur_inst_address s m PC) w4] is replaced by: *)
  sub (reg_content s m PC) w4.

Definition incr_PC (m : processor_mode) (s : state) : option state :=
  Some (update_reg m PC (next_inst_address s m) s).
