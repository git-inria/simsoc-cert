(**
SimSoC-Cert, a Coq library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Bit vectors.
*)

Set Implicit Arguments.

Require Import ZArith.
Require Import Integers. Import Int.
Require Import Util.
Require Import Coqlib.

Open Scope Z_scope.

(****************************************************************************)
(** 32-bits words, masks and bit operations *)
(****************************************************************************)

Notation word := int.

Coercion intval : word >-> Z.

Definition maxu : word := repr max_unsigned.
Definition max : word := repr max_signed.
Definition min : word := repr min_signed.

Notation w0 := zero.
Notation w1 := one.
Definition w2 : word := repr 2.
Definition w4 : word := repr 4.
Definition w8 : word := repr 8.
Definition w12 : word := repr 12.
Definition w15 : word := repr 15.
Definition w31 : word := repr 31.

Definition word_of_bool (b : bool) : word := if b then w1 else w0.

(* mask made of bit [n] *)
Definition mask (n : nat) : word := repr (two_power_nat n).

(* mask made of the bits from bit [n] to bit [n+k] *)
Fixpoint masks_aux (n k : nat) : Z :=
  match k with
    | O => two_power_nat n
    | S k' => two_power_nat n + masks_aux (S n) k'
  end.

(* mask made of the bits from bit [n] to bit [n+(p-n)] *)
Definition masks (n p : nat) : word := repr (masks_aux n (p-n)).

(* test to zero *)
Definition eq_0 (w : word) : word := word_of_bool (zeq 0 w).
Definition ne_0 (w : word) : word := word_of_bool (zne 0 w).

(* bit [k] of [w] *)
Definition bit (k : nat) (w : word) : word := and (mask k) w.
Notation get := bit.

(* tell if bit [k] of [w] is set to 1 *)
Definition is_set (k : nat) (w : word) : bool := zne (bit k w) 0.

(* set bit [k] of [w] to 1 *)
Definition set (k : nat) (w : word) : word := or (mask k) w.

(* set bit [k] of [w] to 0 *)
Definition clear (k : nat) (w : word) : word := and (not (mask k)) w.

(* set bit [k] of [w] to [x] *)
Definition update_bool (k : nat) (b : bool) (w : word) : word :=
  if b then clear k w else set k w.
Definition update (k : nat) (c w : word) : word := update_bool k (zeq c 0) w.

(* bits [k] to [l] of [w] *)
Definition bits (k l : nat) (w : word) : word := and (masks k l) w.
Definition bits_val (k l : nat) (w : word) : Z :=
  bits k l w / two_power_nat k. (*FIXME: use a shift instead*)

(* tell if a signed word is negative *)
Definition is_neg (w : word) : bool := zne (bit 31 w) 0.

(****************************************************************************)
(** n-bits words *)
(****************************************************************************)

(*FIXME: replace bits by generalizing in Integers the type int by
taking wordsize as a parameter?*)

Section bitvec.

Variable n : nat.

Let modulus := two_power_nat n.

Record bitvec : Type := build_bitvec {
  bitvec_val :> Z;
  bitvec_prf : 0 <= bitvec_val < modulus
}.

Lemma bitvec_in_range: forall x, 0 <= Zmod x modulus < modulus.

Proof.
intro x. exact (Z_mod_lt x modulus (two_power_nat_pos n)).
Qed.

Definition mk_bitvec (x : Z) : bitvec := build_bitvec (bitvec_in_range x).

Lemma bitvec_eqdec : forall b1 b2 : bitvec, {b1=b2}+{~b1=b2}.

Proof.
intros [v1 p1] [v2 p2]. case (zeq v1 v2); intro.
left. subst. rewrite (proof_irrelevance _ p1 p2). auto.
right. intro h. inversion h. contradiction.
Qed.

End bitvec.
