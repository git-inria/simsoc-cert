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

Inductive proc_mode : Type := usr.

(****************************************************************************)
(**  Registers *)
(****************************************************************************)

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


Parameter Mbit : nat.
Parameter Qbit : nat.
Parameter Sbit : nat.
Parameter Tbit : nat.

Parameter FPSCR_MASK : nat. (* := 0x003FFFFF.*)

Definition succ := add (repr 1).
Definition pred x := sub x (repr 1).
Definition opp := sub (repr 0).



(* *)

Inductive register : Type :=
| R (k : regnum).

Lemma register_eqdec : forall x y : register, {x=y}+{~x=y}.
Proof.
destruct x; destruct y; intros; try (right; discriminate).
destruct (Regnum.eq_dec k k0). subst. auto.
right. intro h. inversion h. contradiction.
Qed.

Definition reg_mode (m : proc_mode) (k : regnum) : register := R k.

(****************************************************************************)
(** Program status registers *)
(****************************************************************************)

Definition proc_mode_of_word (w : word) : option proc_mode := Some usr.

Inductive instruction_set : Type := SH4.

Definition inst_set (w : word) : option instruction_set := Some SH4.

(****************************************************************************)
(** Exceptions *)
(****************************************************************************)

(****************************************************************************)
(* Exception priorities *)
(****************************************************************************)

(****************************************************************************)
(* The condition field *)
(****************************************************************************)

(****************************************************************************)
(** Condition codes *)
(****************************************************************************)
