(**
SimSoC-Cert, a Coq library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Functions used in the pseudocode, in alphabetical order.
*)

Set Implicit Arguments.

Require Import Coqlib Util Bitvec Arm List.

(**Check f i = b i *)

Definition f := bits_of_Z 32 9.

Eval compute in (f 0 :: f 1 :: f 2 :: f 3 :: f 4 :: nil).

(****************************************************************************)
(** Arithmetic_Shift_Right (p. 1121)

Performs a right shift, repeatedly inserting the original left-most
bit (the sign bit) in the vacated bit positions on the left. *)
(****************************************************************************)

Fixpoint remove_last (x: bool)(l: list bool) :=
  match l with
     nil => nil
    |y :: tl => x :: remove_last y tl
  end.

Inductive rem_last_rel : list bool -> list bool -> Prop :=
| rem_last_intro : forall b0 l, rem_last_rel (l ++ b0 :: nil) l.

Lemma rem_last_correct : forall x l, rem_last_rel (x :: l)(remove_last x l).
Proof. intros x l; revert x. induction l as [|y l Hind].
  simpl. intro x. exact (rem_last_intro x nil).
  simpl. intro x. case (Hind y); clear Hind l.
  intros b0 l. exact (rem_last_intro b0 (x :: l)).
Qed.
   
Definition copy_first (x: bool)(l: list bool) := x :: x :: l.

Inductive copy_first_rel : list bool -> list bool -> Prop :=
| copy_first_intro : forall b l, copy_first_rel (b :: l) (b :: b :: l).

Lemma copy_first_correct: forall x l, copy_first_rel (x :: l) (copy_first x l).
Proof. intros x l. unfold copy_first. exact (copy_first_intro x l).
Qed.

Theorem len_remove_last_1: forall x l, S(length (remove_last x l)) = length (remove_last x (x :: l)).
Proof. intros x l. simpl. auto.
Qed.

Theorem len_remove_last_2: forall (x a: bool)(l: list bool),length (remove_last x l) = length (remove_last a l).
Proof. intros x a l. induction l. auto. simpl. auto.
Qed.

Lemma len_remove_last: forall x l, length l = length (remove_last x l).
Proof. intros. induction l.  auto. 
 simpl. rewrite IHl. rewrite len_remove_last_2 with x a l. auto.
Qed.

Lemma remove_last_eq: forall x l, l = nil -> remove_last x l = nil.
Proof. intros. rewrite H. simpl. auto.
Qed.
 
Lemma len_remove_last_nil : forall x, List.length (remove_last x nil) = 0%nat.
Proof. intros. simpl. auto.
Qed.

Lemma len_copy_first_1: forall x l, S(length (copy_first x l)) = length (copy_first x (x :: l)).
Proof. intros. simpl. auto. 
Qed.

Lemma len_copy_first_2: forall (x a : bool) (l: list bool), length (copy_first x l) = length (copy_first a l).
Proof. intros. simpl. auto. 
Qed.

Definition ASR' (x y: bool)(l: list bool) :=
  let result := remove_last x (y :: l) in
    match result with
      |nil => nil
      |z :: r => copy_first z r
    end.

Definition ASR1' (l : list bool) :=
  match l with
    |nil => nil
    |hd :: tl => 
      match tl with
        |nil => (hd::nil)
        |a :: b => ASR' hd a b
      end
  end. 

(* Provides the value of the n-th bit of some word *)

Definition bit (n : Z) (w : word) : bool := bits_of_Z wordsize w n.

(* Logical_Shift_Left *)

Definition LSL1 (w w' : word) : Prop :=
  bit 0 w' = false
  /\ forall i, 1 <= i <= 31 -> bit i w' = bit (i-1) w.

Fixpoint LSL (w : word) (n : nat) (w' : word) : Prop :=
  match n with
    | O => w' = w
    | S n' => exists w1, LSL w n' w1 /\ LSL1 w1 w'
  end.

(*Inductive LSL : word -> nat -> word -> Prop :=
| LSL0 : forall w, LSL w 0 w
| LSLS : forall w n' w1 w', LSL w n' w1 -> LSL1 w1 w' -> LSL w (S n') w'.*)

Lemma LSL_correct : forall w n, LSL w n (shl w (repr (Z_of_nat n))).

Proof.
induction n.
(* case 0 *)
simpl. unfold shl.
(* case S *)

(* Arithmetic_Shift_Right *)

Definition ASR1 (w w' : word) : Prop :=
  bit 31 w' = bit 31 w
  /\ forall i, 0 <= i <= 30 -> bit i w' = bit (i+1) w.

Fixpoint ASR (w : word) (n : nat) (w' : word) : Prop :=
  match n with
    | O => w' = w
    | S n' => exists w1, ASR w n' w1 /\ ASR1 w1 w'
  end.

Lemma ASR_correct : forall w n, ASR w n (shr w (repr (Z_of_nat n))).

