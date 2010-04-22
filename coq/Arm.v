(**
SimSoC-Cert, a Coq library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Basic types and functions for describing the ARM state
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

Definition reg_mode (m : proc_mode) (k : regnum) : register :=
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

Definition exception_mode (e : exception) : exn_mode :=
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

Definition exception_vector_address (e : exception) (use_high_vectors : bool)
  : Z :=
  match use_high_vectors with
    | false =>
      match e with
        | Reset =>     (*0x00000000*)  0
        | UndIns =>    (*0x00000004*)  4
        | SoftInt =>   (*0x00000008*)  8
        | PFAbort =>   (*0x0000000C*) 12
        | ImpAbort (*FIXME?*)
        | DataAbort => (*0x00000010*) 16
(*FIXME: depends on VE bit in the system control coprocessor *)
        | IRQ =>       (*0x00000018*) 24
        | FIQ =>       (*0x0000001C*) 28
      end
    | true =>
      match e with
        | Reset =>     (*0xFFFF0000*)
          Zpos 1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0
        | UndIns =>    (*0xFFFF0004*)
          Zpos 1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0~0
        | SoftInt =>   (*0xFFFF0008*)
          Zpos 1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~0~0~0~0~0~0~0~0~0~0~0~1~0~0~0
        | PFAbort =>   (*0xFFFF000C*)
          Zpos 1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~0~0~0~0~0~0~0~0~0~0~0~1~1~0~0
        | ImpAbort (*FIXME?*)
        | DataAbort => (*0xFFFF0010*)
          Zpos 1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~0~0~0~0~0~0~0~0~0~0~1~0~0~0~0
(*FIXME: depends on VE bit in the system control coprocessor *)
        | IRQ =>       (*0xFFFF0018*)
          Zpos 1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~0~0~0~0~0~0~0~0~0~0~1~1~0~0~0
        | FIQ =>       (*0xFFFF001C*)
          Zpos 1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~0~0~0~0~0~0~0~0~0~0~1~1~1~0~0
      end
  end.

(****************************************************************************)
(* Exception priorities (p. 63) *)
(****************************************************************************)

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

(*WARNING: by using this functions, exceptions are always sorted from
the highest priority to the lowest, so that the exception with highest
priority is the first one *)

Fixpoint insert (e : exception) (l : list exception) : list exception :=
  match l with
    | nil => e :: nil
    | e' :: l' => if zlt (priority e) (priority e') then e :: l
      else e' :: insert e l'
  end.

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

Fixpoint condition (w : word) : opcode :=
  match bits_val 31 28 w with
    | Z0           => EQ
    | Zpos       1 => NE
    | Zpos     1~0 => CS
    | Zpos     1~1 => CC
    | Zpos   1~0~0 => MI
    | Zpos   1~0~1 => PL
    | Zpos   1~1~0 => VS
    | Zpos   1~1~1 => VC
    | Zpos 1~0~0~0 => HI
    | Zpos 1~0~0~1 => LS
    | Zpos 1~0~1~0 => GE
    | Zpos 1~0~1~1 => LT
    | Zpos 1~1~0~0 => GT
    | Zpos 1~1~0~1 => LE
    | Zpos 1~1~1~0 => AL
    | _ => UN
  end.
