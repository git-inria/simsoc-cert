(**
SimSoC-Cert, a toolkit for generating certified processor simulators.

See the COPYRIGHTS and LICENSE files.

Miscellaneous definitions and lemmas extending the Coq standard library.
*)

Set Implicit Arguments.

Require Import Bool List ZArith Integers NaryFunctions.
Import Int.

Open Scope Z_scope.

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
(** two_power_nat *)
(****************************************************************************)

(*FIXME: to be finished*)
Lemma two_power_nat_monotone : forall x y, two_power_nat x <= two_power_nat y.

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
(** list constructor *)
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

nary_iter_incr f n k x = x (f k) (f (k+1)) .. (f (k+n-1))

nary_iter_decr f n k x = x (f k) (f (k-1)) .. (f (k-n+1)) *)
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
(** dependent list constructor *)
(****************************************************************************)
Require Import Bvector.

Notation "{{ }}" := (Vnil _).
Notation "{{ a ; .. ; b }}" := (Vcons _ a _ .. (Vcons _ b _ (Vnil _)) ..).

(* Convert a [vector] into a [list] with an extra property on its length. *)
Definition list_of_vector : forall A n, vector A n -> { l : list A | n = length l }.
  induction n ; intros.
  exists nil.
  trivial.
  inversion X.
  destruct (IHn X0).
  exists (a :: x).
  simpl.
  auto.
Defined.

(* Simple application of an n-ary function with its parameters in the list. *)
Definition apply {A n B} (f : NaryFunctions.nfun A n B) (l : vector A n) : B.
  refine (NaryFunctions.nuncurry _ _ _ f _).
  destruct (list_of_vector l).
  rewrite e.
  apply NaryFunctions.nprod_of_list.
Defined.
