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

Definition zne (x y : Z) : bool := if Z_eq_dec x y then false else true.

(****************************************************************************)

Notation beq := eqb.

Definition bne (x y : bool) : bool := negb (eqb x y).

(****************************************************************************)

Lemma between_dec : forall a x b, {a <= x <= b}+{~(a <= x <= b)}.

Proof.
intros. case (Z_le_dec a x); intro. case (Z_le_dec x b); intro.
left. auto. right. intros [h1 h2]. contradiction.
right. intros [h1 h2]. contradiction.
Defined.

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

Section update_map.

Variables (A : Type) (eqdec : forall x y : A, {x=y}+{~x=y}) (B : Type).

Definition update_map (a : A) (b : B) (f : A -> B) : A -> B :=
  fun x => if eqdec x a then b else f x.

End update_map.
