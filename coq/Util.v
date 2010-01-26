(**
SimSoC-Cert, a Coq library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Miscellaneous definitions and lemmas extending the Coq standard library.
*)

Set Implicit Arguments.

Require Import ZArith.
Require Import Bool.

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
(** generic update function *)
(****************************************************************************)

Section update_map.

Variables (A : Type) (eqdec : forall x y : A, {x=y}+{~x=y}) (B : Type).

Definition update_map (a : A) (b : B) (f : A -> B) : A -> B :=
  fun x => if eqdec x a then b else f x.

End update_map.
