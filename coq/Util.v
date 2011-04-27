(**
SimSoC-Cert, a toolkit for generating certified processor simulators.

See the COPYRIGHTS and LICENSE files.

Miscellaneous definitions and lemmas extending the Coq standard library.
*)

Set Implicit Arguments.

Require Import Bool List ZArith Integers NaryFunctions Coqlib.
Import Int.

Open Scope Z_scope.

Implicit Arguments orb_true_elim [b1 b2].

(****************************************************************************)
(** tactics *)
(****************************************************************************)

Ltac refl := reflexivity.
Ltac discr := discriminate.
Ltac hyp := assumption.

(****************************************************************************)
(** properties of boolean operators *)
(****************************************************************************)

Lemma false_not_true : forall b, b = false <-> ~(b = true).

Proof.
  destruct b; intuition.
Qed.

(****************************************************************************)
(** boolean equality on [positive] *)
(****************************************************************************)

Definition beq_positive := Peqb.

Lemma beq_positive_ok : forall x y, beq_positive x y = true <-> x = y.

Proof.
unfold beq_positive. induction x; destruct y; simpl; intuition; try discr.
rewrite IHx in H. subst. refl.
rewrite IHx. inversion H. refl.
rewrite IHx in H. subst. refl.
rewrite IHx. inversion H. refl.
Qed.

(****************************************************************************)
(** boolean comparison functions on integers *)
(****************************************************************************)

Definition zeq (x y : Z) : bool := if Z_eq_dec x y then true else false.
Definition zne (x y : Z) : bool := negb (zeq x y).
Definition zlt (x y : Z) : bool := if Z_lt_ge_dec x y then true else false.
Definition zge (x y : Z) : bool := negb (zlt x y).
Definition zgt (x y : Z) : bool := zlt y x.
Definition zle (x y : Z) : bool := negb (zgt x y).

(****************************************************************************)
(** boolean comparison functions on booleans *)
(****************************************************************************)

Notation beq := eqb.

Definition bne (x y : bool) : bool := negb (eqb x y).

(****************************************************************************)
(** decidability of a <= _ <= b *)
(****************************************************************************)

Lemma between_dec : forall a x b, {a <= x <= b}+{~(a <= x <= b)}.

Proof.
  intros. case (Z_le_dec a x); intro. case (Z_le_dec x b); intro.
  left. auto. right. intros [h1 h2]. contradiction.
  right. intros [h1 h2]. contradiction.
Defined.

(****************************************************************************)
(** converts a positive integer into a natural number *)
(****************************************************************************)

Definition nat_of_Z (x : Z) : nat :=
  match x with
    | Zpos p => nat_of_P p
    | _ => O
  end.

Lemma nat_of_Z_ok : forall x : Z, x >= 0 -> Z_of_nat (nat_of_Z x) = x.

Proof.
  destruct x; simpl.
    reflexivity.
    intros _. rewrite Zpos_eq_Z_of_nat_o_nat_of_P. reflexivity.
    compute. intro n; case n; reflexivity.
Qed.

(****************************************************************************)
(** properties of two_power_nat *)
(****************************************************************************)

(*FIXME: to be done*)
Lemma two_power_nat_mon : forall x y, two_power_nat x <= two_power_nat y.

Proof.
Abort.

(****************************************************************************)
(** generic update function *)
(****************************************************************************)

Section update_map.

  Variables (A : Type) (eqdec : forall x y : A, {x=y}+{~x=y}) (B : Type).

  Definition update_map (f : A -> B) (a : A) (b : B) : A -> B :=
    fun x => if eqdec x a then b else f x.

End update_map.

(****************************************************************************)
(** [clist a k] builds a list of [a]'s of length [k] *)
(****************************************************************************)

Section clist.

Variables (A : Type) (a : A).

Fixpoint clist (k : nat) : list A :=
  match k with
    | O => nil
    | S k' => a :: clist k'
  end.

End clist.

(****************************************************************************)
(** convert a word into a list of booleans of length 32 *)
(****************************************************************************)

Fixpoint bools_of_positive (p : positive) (acc : list bool) : list bool :=
  match p with
    | xI p' => bools_of_positive p' (true :: acc)
    | xO p' => bools_of_positive p' (false :: acc)
    | xH => true :: acc
  end.

Definition bools_of_word (w : int) : list bool :=
  match unsigned w with
    | Zpos p => let l := bools_of_positive p nil in
      clist false (wordsize - length l) ++ l
    | _ => clist false wordsize
  end.

(****************************************************************************)
(** build an nary-application by iterating some function:
- nary_iter_incr f n k x = x (f k) (f (k+1)) .. (f (k+n-1))
- nary_iter_decr f n k x = x (f k) (f (k-1)) .. (f (k-n+1)) *)
(****************************************************************************)

Section nary.

  Variables (A : Type) (f : Z -> A) (B : Type).

  Fixpoint nary_iter_incr n k : A^^n --> B -> B :=
    match n as n return A^^n --> B -> B with
      | O => fun x => x
      | S n' => fun x => nary_iter_incr n' (k+1) (x (f k))
    end.

  Fixpoint nary_iter_decr n k : A^^n --> B -> B :=
    match n as n return A^^n --> B -> B with
      | O => fun x => x
      | S n' => fun x => nary_iter_decr n' (k-1) (x (f k))
    end.

End nary.

Implicit Arguments nary_iter_incr [A B].
Implicit Arguments nary_iter_decr [A B].

(****************************************************************************)
(** notation for vectors *)
(****************************************************************************)

Require Import Bvector.

Notation "{{ }}" := (Vnil _).
Notation "{{ a ; .. ; b }}" := (Vcons _ a _ .. (Vcons _ b _ (Vnil _)) ..).

(****************************************************************************)
(* convert a [vector] of size [n] into a [list] of length [n] *)
(****************************************************************************)

Definition list_of_vector : forall A n,
  vector A n -> { l : list A | n = length l }.

Proof.
  induction n; intros.
  exists nil. trivial.
  inversion X. destruct (IHn X0). exists (a :: x). simpl. auto.
Defined.

(****************************************************************************)
(* application of an n-ary function to a vector of n arguments *)
(****************************************************************************)

Definition apply {A n B} (f : NaryFunctions.nfun A n B) (l : vector A n) : B.

Proof.
  refine (NaryFunctions.nuncurry _ _ _ f _). destruct (list_of_vector l).
  rewrite e. apply NaryFunctions.nprod_of_list.
Defined.

(****************************************************************************)
(** convert a decidability lemma into a boolean function *)
(****************************************************************************)

Section prop_dec.

  Variables (A : Type) (P : A -> Prop) (Pdec : forall x, {P x}+{~P x}).

  Definition bP x :=
    match Pdec x with
      | left _ => true
      | right _ => false
    end.

  Lemma bP_ok : forall x, bP x = true <-> P x.

  Proof.
    intro x. unfold bP. case (Pdec x); intuition. discriminate.
  Qed.

End prop_dec.

Implicit Arguments bP [A P].
Implicit Arguments bP_ok [A P].

(****************************************************************************)
(** boolean functions on lists *)
(****************************************************************************)

Section list.

  Variables (A : Type) (beq : A -> A -> bool)
    (beq_ok : forall x y, beq x y = true <-> x = y).

  Lemma beq_refl : forall x, beq x x = true.

  Proof.
    intro. rewrite (beq_ok x x). auto.
  Qed.

(****************************************************************************)
(** membership (taken from CoLoR) *)
(****************************************************************************)

  Fixpoint mem (x : A) (l : list A) : bool :=
    match l with
      | nil => false
      | y :: m => beq x y || mem x m
    end.

  Lemma mem_ok : forall x l, mem x l = true <-> In x l.

  Proof.
    induction l; simpl; intros; auto. intuition. split; intro.
    destruct (orb_true_elim H). rewrite beq_ok in e. subst. auto. intuition.
    destruct H. subst. rewrite beq_refl. auto. intuition.
  Qed.

(****************************************************************************)
(** list_norepet (taken from CoLoR [repeat_free]) *)
(****************************************************************************)

  Fixpoint blist_norepet (l : list A) : bool :=
    match l with
      | nil => true
      | a :: l' => negb (mem a l') && blist_norepet l'
    end.

  Lemma blist_norepet_ok : forall l, blist_norepet l = true <-> list_norepet l.

  Proof.
    induction l; simpl; intros.
    intuition. apply list_norepet_nil.
    rewrite andb_true_iff, IHl, negb_true_iff, false_not_true, mem_ok.
    split; intro H.
    destruct H as [ha hl]. apply list_norepet_cons; hyp.
    inversion H. intuition.
  Qed.

End list.

Implicit Arguments blist_norepet_ok [A beq].

(****************************************************************************)
(** tactics *)
(****************************************************************************)

Ltac check_eq := vm_compute; refl.

Ltac list_norepet beq_ok := rewrite <- (blist_norepet_ok beq_ok); check_eq.
