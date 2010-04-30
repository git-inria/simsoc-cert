(**
SimSoC-Cert, a Coq library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Bit vectors.
*)

Set Implicit Arguments.

Require Import Util ZArith Coqlib.
Require Export Integers. Export Int.

(****************************************************************************)
(** 32-bits words, masks and bit operations *)
(****************************************************************************)

Notation word := int.

Coercion intval : word >-> Z.

Notation w0 := zero.
Notation w1 := one.

Definition word_of_bool (b : bool) : word := if b then w1 else w0.

Coercion word_of_bool : bool >-> word.

(* mask made of the bits n to n+k *)
Fixpoint masks_aux (n k : nat) : Z :=
  match k with
    | O => two_power_nat n
    | S k' => two_power_nat n + masks_aux (S n) k'
  end.

(* mask made of the bits n to n+(p-n) (p>=n) *)
Definition masks (p n : nat) : word := repr (masks_aux n (p-n)).
Definition anti_masks p n := not (masks p n).

(* mask made of bit n *)
Definition mask n := masks n n.
Definition anti_mask n := anti_masks n n.

(* word made of the bits p to n of w (p>=n) *)
Definition bits_val (p n : nat) (w : word) : Z :=
  and (masks p n) w / two_power_nat n.
Definition bits (p n : nat) (w : word) : word := repr (bits_val p n w).
Notation "w [ p # n ]" := (bits p n w) (at level 8).

(* n-th bit of w *)
Definition bit (n : nat) (w : word) : word := bits n n w.
Notation get := bit.
Notation "w [ n ]" := (bit n w) (at level 8).

(* tell if w[n] is set to 1 *)
Definition is_set (n : nat) (w : word) : bool := zne w[n] 0.

(* tell if a signed word is negative *)
Definition is_neg (w : word) : bool := is_set 31 w.

(* set w[n] to 1 *)
Definition set (n : nat) (w : word) : word := or (mask n) w.

(* set w[n] to 0 *)
Definition clear (n : nat) (w : word) : word := and (anti_mask n) w.

(* set w[n] to 1 if b=true, and 0 if b=false *)
Definition set_bit_aux (n : nat) (b : bool) (w : word) : word :=
  if b then set n w else clear n w.

(* set w[n] to 1 if v<>0, and 0 if v=0 *)
Definition set_bit (n : nat) (v w : word) : word := set_bit_aux n (zne v 0) w.

(* set w[p:p-k] to v[k:0] *)
Fixpoint set_bits_aux (p k : nat) (v w : word) : word :=
  match k with
    | O => set_bit p v[0] w
    | S k' => set_bits_aux (pred p) k' v (set_bit p v[k] w)
  end.

(* set w[p:n] to v[p-n:0] (p>=n) *)
Definition set_bits (p n : nat) (v w : word) : word :=
  set_bits_aux p (p-n) v w.

(****************************************************************************)
(** n-bits words *)
(****************************************************************************)

(*IMPROVE: replace bits by generalizing in Integers the type int by
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

(*IMPROVE: to be improved when n<=32*)
Definition word_of_bitvec (v : bitvec) : word := repr v.

Coercion word_of_bitvec : bitvec >-> word.

End bitvec.

(****************************************************************************)
(** A2.1 Data types (p. 39) *)
(****************************************************************************)

Inductive size : Type := Word | Half | Byte.

Definition byte_size := 8%nat.
Definition byte := bitvec byte_size.
Definition mk_byte := mk_bitvec byte_size.

Definition get_byte0 w := mk_byte (intval w[7#0]).
Definition get_byte1 w := mk_byte (intval w[15#8]).
Definition get_byte2 w := mk_byte (intval w[23#16]).
Definition get_byte3 w := mk_byte (intval w[31#24]).

Definition half_size := 16%nat.
Definition half := bitvec half_size.
Definition mk_half := mk_bitvec half_size.

Definition get_half0 w := mk_half (intval w[15#0]).
Definition get_half1 w := mk_half (intval w[31#16]).

(****************************************************************************)
(** A2.3 Registers (p. 42) *)
(****************************************************************************)

Definition regnum_size := 4%nat.
Definition regnum := bitvec regnum_size.
Definition mk_regnum := mk_bitvec regnum_size.

Definition PC := mk_regnum 15.
Definition LR := mk_regnum 14.
Definition SP := mk_regnum 13.

(*IMPROVE: can be improved by using build_bitvec instead of mk_bitvec
since [bits (k+3) k w] is always smaller than [two_power_nat 4]*)
Definition regnum_from_bit (k : nat) (w : word) : regnum :=
  mk_regnum (bits (k+3) k w).

(****************************************************************************)
(** Addresses (p. 68) *)
(****************************************************************************)

Definition address_size := 30%nat.
Definition address := bitvec address_size.
Definition mk_address := mk_bitvec address_size.
Definition address_eqdec := @bitvec_eqdec address_size.

(*IMPROVE: can be improved by using build_bitvec instead of mk_bitvec
since [bits 31 2 w] is always smaller than [two_power_nat 30]*)
Definition address_of_word (w : word) : address :=
  mk_address (bits 31 2 w).

(****************************************************************************)
(** 64-bits words *)
(****************************************************************************)

Definition long_size := 64%nat.
Definition long := bitvec long_size.
Definition mk_long := mk_bitvec long_size.
