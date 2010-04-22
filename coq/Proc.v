(**
SimSoC-Cert, a Coq library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Processor state.
*)

Set Implicit Arguments.

Require Import Bitvec ZArith Coqlib Util Integers.
Import Int.

Open Scope Z_scope.

(****************************************************************************)
(** A2.2 Processor modes (p. 41) *)
(****************************************************************************)

Inductive exn_mode : Type := fiq | irq | svc | abt | und.

Lemma opt_exn_mode_eqdec : forall x y : option exn_mode, {x=y}+{~x=y}.

Proof. decide equality. decide equality. Qed.

Inductive proc_mode : Type := usr | exn (m : exn_mode) | sys.

Definition word_of_proc_mode (m : proc_mode) : word := repr (Zpos
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

Inductive register : Type :=
| R (k : regnum)
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

Definition reg_of_exn_mode (m : exn_mode) (k : regnum)
  : register :=
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

Definition reg_of_mode (m : proc_mode) (k : regnum) : register :=
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

Definition proc_mode_of_word (w : word) : option proc_mode :=
  match Mbits w with
    | Zpos 1~0~0~0~0 => Some usr
    | Zpos 1~0~0~0~1 => Some (exn fiq)
    | Zpos 1~0~0~1~0 => Some (exn irq)
    | Zpos 1~0~0~1~1 => Some (exn svc)
    | Zpos 1~0~1~1~1 => Some (exn abt)
    | Zpos 1~1~0~1~1 => Some (exn und)
    | Zpos 1~1~1~1~1 => Some sys
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

(*IMPROVE: by allowing heading 0's? *)

Fixpoint condition (w : word) :=
  match bits_val 31 28 w with
    | Z0 => EQ
    | Zpos 1 => NE
    | Zpos 1~0 => CS
    | Zpos 1~1 => CC
    | Zpos 1~0~0 => MI
    | Zpos 1~0~1 => PL
    | Zpos 1~1~0 => VS
    | Zpos 1~1~1 => VC
    | Zpos 1~0~0~0 => HI
    | Zpos 1~0~0~1 => LS
    | Zpos 1~0~1~0 => GE
    | Zpos 1~0~1~1 => LT
    | Zpos 1~1~0~0 => GT
    | Zpos 1~1~0~1 => LE
    | Zpos 1~1~1~0 => AL
    | _ => UN
  end.

(****************************************************************************)
(** Processor state *)
(****************************************************************************)

(*BEWARE: invariant to preserve:
proc_mode_of_word (cpsr s) = Some m -> mode s = m.
To preserve this invariant,
always use the function set_cpsr defined hereafter. *)

Record state : Type := mk_state {
  (* Current program status register *)
  cpsr : word;
  (* Saved program status registers *)
  spsr : option exn_mode -> word;
  (* Registers *)
  reg : register -> word;
  (* Raised exceptions *)
  exns : list exception;
  (* Processor mode *)
  mode : proc_mode
}.

Definition set_cpsr (s : state) (w : word) : state :=
  match proc_mode_of_word w with
    | Some m => mk_state w (spsr s) (reg s) (exns s) m
    | None => mk_state w (spsr s) (reg s) (exns s) (mode s) (*FIXME?*)
  end.

Definition set_spsr (s : state) (o : option exn_mode) (w : word) : state :=
  mk_state (cpsr s)
  (update_map opt_exn_mode_eqdec (spsr s) o w)
  (reg s) (exns s) (mode s).

Definition set_reg_of_mode (s : state) (m : proc_mode) (k : regnum) (w : word)
  : state :=
  mk_state (cpsr s) (spsr s)
  (update_map register_eqdec (reg s) (reg_of_mode m k) w)
  (exns s) (mode s).

Definition set_reg (s : state) (k : regnum) (w : word) : state :=
  set_reg_of_mode s (mode s) k w.

Definition reg_content_of_mode (s : state) (m : proc_mode) (k : regnum)
  : word := reg s (reg_of_mode m k).

Definition reg_content (s : state) (k : regnum) : word :=
  reg_content_of_mode s (mode s) k.

Definition set_exns (s : state) (es : list exception) : state :=
  mk_state (cpsr s) (spsr s) (reg s) es (mode s).
(*REMARK: Exception provides a function "add_exn" *)

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
