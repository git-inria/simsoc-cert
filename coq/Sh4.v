(**
SimSoC-Cert, a Coq library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the SH4 architecture following the:

SH-4, Software Manual, Renesas 32-Bit RISC, Rev.6.00 2006.09

Page numbers refer to Renesas_SH4_2006.pdf.

Basic types and functions for describing the SH4 state.
*)

Set Implicit Arguments.

Require Import Bitvec ZArith Coqlib Util.

(****************************************************************************)
(** Processor modes *)
(****************************************************************************)

Inductive proc_mode : Type := usr | sys.

Definition word_of_proc_mode (m : proc_mode) : word := repr (Zpos
  (match m with
     | usr => 1~0~0~0~0
     | sys => 1~1~1~1~1
   end)).

(****************************************************************************)
(**  Registers *)
(****************************************************************************)

(*Definition PC := mk_regnum 15.*)
Definition LR := mk_regnum 14.
Definition SP := mk_regnum 13.

Parameter DBR : regnum.
Parameter EXPEVT : regnum.
Parameter FPSCR : regnum.
Parameter FPUL : regnum.
Parameter GBR : regnum.
Parameter H_00000100 : regnum.
Parameter MACH : regnum.
Parameter MACL : regnum.
Parameter PC : regnum.
Parameter PR : regnum.
Parameter PTEA : regnum.
Parameter PTEH : regnum.
Parameter PTEL : regnum.
Parameter R0_BANK : regnum.
Parameter R1_BANK : regnum.
Parameter R2_BANK : regnum.
Parameter R3_BANK : regnum.
Parameter R4_BANK : regnum.
Parameter R5_BANK : regnum.
Parameter R6_BANK : regnum.
Parameter R7_BANK : regnum.
Parameter SGR : regnum.
Parameter SPC : regnum.
Parameter SR : regnum.
Parameter SR_BL : regnum.
Parameter SR_MD : regnum.
Parameter SR_RB : regnum.
Parameter SSR : regnum.
Parameter TRA : regnum.
Parameter VBR : regnum.


Definition succ := add (repr 1).
Definition pred x := sub x (repr 1).
Definition opp := sub (repr 0).
Parameter Mbit : nat.
Parameter Qbit : nat.
Parameter Sbit : nat.
Parameter Tbit : nat.
Parameter FPSCR_MASK : nat. (* := 0x003FFFFF *)




Inductive register : Type :=
| R (k : regnum).

Lemma register_eqdec : forall x y : register, {x=y}+{~x=y}.

Proof.
destruct x; destruct y; intros; try (right; discriminate).
destruct (Regnum.eq_dec k k0). subst. auto.
right. intro h. inversion h. contradiction.
Qed.

Definition reg_mode (m : proc_mode) (k : regnum) : register :=
  match m with
    | usr | sys => R k
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

(*Definition Qbit := 27%nat.*)

(* The GE bits (p. 51) *)

Definition GEbits := bits_val 19 16.

(* The E bit (p. 51) *)

Definition Ebit := 9%nat.

(* The interrupt disable bits (p. 52) *)

Definition Abit := 8%nat.
Definition Ibit := 7%nat.
Definition Fbit := 6%nat.

(* Mode bits (p. 52) *)

Definition Mbits := bits_val 4 0.

Definition proc_mode_of_word (w : word) : option proc_mode :=
  match Mbits w with
    | Zpos 1~0~0~0~0 => Some usr
    | Zpos 1~1~1~1~1 => Some sys
    | _ => None
  end.

(* The T and J bits (p. 53) *)

(*Definition Tbit := 5%nat.*)
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

(*WARNING: by using this function, exceptions are always sorted from
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
| HI | LS | GE | LT | GT | LE | AL.

Notation HS := CS.
Notation LO := CC.

(****************************************************************************)
(** Table A3-1 Condition codes (p. 112) *)
(****************************************************************************)

Fixpoint condition (w : word) : option opcode :=
  match bits_val 31 28 w with
    | Z0           => Some EQ
    | Zpos       1 => Some NE
    | Zpos     1~0 => Some CS
    | Zpos     1~1 => Some CC
    | Zpos   1~0~0 => Some MI
    | Zpos   1~0~1 => Some PL
    | Zpos   1~1~0 => Some VS
    | Zpos   1~1~1 => Some VC
    | Zpos 1~0~0~0 => Some HI
    | Zpos 1~0~0~1 => Some LS
    | Zpos 1~0~1~0 => Some GE
    | Zpos 1~0~1~1 => Some LT
    | Zpos 1~1~0~0 => Some GT
    | Zpos 1~1~0~1 => Some LE
    | Zpos 1~1~1~0 => Some AL
    | _ => None
  end.
