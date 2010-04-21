(**
SimSoC-Cert, a Coq library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Processor state.
*)

Set Implicit Arguments.

Require Import Bitvec.
Require Import ZArith.
Require Import Coqlib.
Require Import Util.
Require Import Integers. Import Int.

Open Scope Z_scope.

(****************************************************************************)
(** A2.2 Processor modes (p. 41) *)
(****************************************************************************)

Inductive processor_exception_mode : Type := fiq | irq | svc | abt | und.

Lemma processor_exception_mode_eqdec :
  forall x y : option processor_exception_mode, {x=y}+{~x=y}.

Proof. decide equality.  decide equality. Qed.

Inductive processor_mode : Type :=
  usr | exn (m : processor_exception_mode) | sys.

Definition word_of_processor_mode (m : processor_mode) : word := repr (Zpos
  (match m with
     | usr => 1~0~0~0~0
     | exn e =>
       match e with
         | fiq => 1~0~0~0~1
         | irq => 1~0~0~1~0
         | svc => 1~0~0~1~1
         | abt => 1~0~1~1~1
         | und => 1~1~0~1~1
       end
     | sys => 1~1~1~1~1
   end)).

(****************************************************************************)
(** A2.3 Registers (p. 42) & A2.4 General-purpose registers (p. 44) *)
(****************************************************************************)

Definition reg_num := bitvec 4.
Definition mk_reg_num := mk_bitvec 4.

Definition PC := mk_reg_num 15.
Definition LR := mk_reg_num 14.
Definition SP := mk_reg_num 13.

(*IMPROVE: can be improved by using build_bitvec instead of mk_bitvec
since [bits_val k (k+3) w] is always smaller than [two_power_nat 4]*)
Definition reg_num_from_bit (k : nat) (w : word) : reg_num :=
  mk_reg_num (bits_val k (k+3) w).

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
destruct (Z_eq_dec k k0). subst. rewrite (proof_irrelevance _ h0 h). auto.
right. intro p. inversion p. contradiction.
destruct (Z_eq_dec k k0). subst. rewrite (proof_irrelevance _ h0 h). auto.
right. intro p. inversion p. contradiction.
destruct (Z_eq_dec k k0). subst. rewrite (proof_irrelevance _ h0 h). auto.
right. intro p. inversion p. contradiction.
destruct (Z_eq_dec k k0). subst. rewrite (proof_irrelevance _ h0 h). auto.
right. intro p. inversion p. contradiction.
destruct (Z_eq_dec k k0). subst. rewrite (proof_irrelevance _ h0 h). auto.
right. intro p. inversion p. contradiction.
Qed.

Definition reg_of_exn_mode (m : processor_exception_mode)
  (k : reg_num) : register :=
  match m with
    | svc =>
      match between_dec 13 k 14 with
        | left h => R_svc h
        | _  => R k
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

Definition processor_mode_of_word (w : word) : option processor_mode :=
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

(****************************************************************************)
(* A3.2 The condition field (p. 111) *)
(****************************************************************************)

Inductive opcode : Type :=
| EQ | NE | CS | CC | MI | PL | VS | VC
| HI | LS | GE | LT | GT | LE | AL | UN.

Notation HS := CS.
Notation LO := CC.

(****************************************************************************)
(** Table A3-1 Condition codes (p. 112) *)
(****************************************************************************)

Fixpoint condition (w : word) :=
  match bits_val 31 28 w with
    | 0 => EQ
    | 1 => NE
    | 2 => CS
    | 3 => CC
    | 4 => MI
    | 5 => PL
    | 6 => VS
    | 7 => VC
    | 8 => HI
    | 9 => LS
    | 10 => GE
    | 11 => LT
    | 12 => GT
    | 13 => LE
    | 14 => AL
    | _ => UN
  end.

(****************************************************************************)
(** Processor state *)
(****************************************************************************)

(*BEWARE: invariant to preserve:
processor_mode_of_word (cpsr s) = Some m -> mode s = m.
To preserve this invariant,
always use the function update_cpsr defined hereafter. *)

Record state : Type := mk_state {
  (* Current program status register *)
  cpsr : word;
  (* Saved program status registers *)
  spsr : option processor_exception_mode -> word;
  (* Registers *)
  reg : register -> word;
  (* Raised exceptions *)
  exns : list exception;
  (* Processor mode *)
  mode : processor_mode
}.

Definition reg_content (s : state) (k : reg_num) :=
  reg s (reg_of_mode (mode s) k).

Definition set_cpsr s x :=
  match processor_mode_of_word x with
    | Some m => mk_state x (spsr s) (reg s) (exns s) m
    | None => mk_state x (spsr s) (reg s) (exns s) (mode s) (*FIXME?*)
  end.

Definition set_spsr s x := mk_state (cpsr s) x (reg s) (exns s) (mode s).
Definition set_reg s x := mk_state (cpsr s) (spsr s) x (exns s) (mode s).
Definition set_exns s x := mk_state (cpsr s) (spsr s) (reg s) x (mode s).

Definition update_map_spsr m w s :=
  update_map processor_exception_mode_eqdec m w (spsr s).
Definition update_map_reg k w s :=
  update_map register_eqdec (reg_of_mode (mode s) k) w (reg s).

Definition update_cpsr w s := set_cpsr s w.
Definition update_spsr m w s := set_spsr s (update_map_spsr m w s).
Definition update_reg k w s := set_reg s (update_map_reg k w s).

(****************************************************************************)
(** Current instruction address
cf. A2.4.3 Register 15 and the program counter,
Reading the program counter (p. 47) *)
(****************************************************************************)

(*IMPROVE: add cur_inst_address as new field in state?*)
Definition cur_inst_address (s : state) : word := sub (reg_content s PC) w8.

(****************************************************************************)
(** Next instruction address
cf. A2.7.1 Address space (p. 70) *)
(****************************************************************************)

Definition next_inst_address (s : state) : word :=
  (*REMARK: [add (cur_inst_address s m PC) w4] is replaced by: *)
  sub (reg_content s PC) w4.
