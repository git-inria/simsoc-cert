(**
SimSoC-Cert, a Coq library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Bit vectors.
*)

Set Implicit Arguments.

Require Import ZArith Integers Util Coqlib.
Import Int.

Open Scope Z_scope.

(****************************************************************************)
(** 32-bits words, masks and bit operations *)
(****************************************************************************)

Notation word := int.

Coercion intval : word >-> Z.

Notation w0 := zero.
Notation w1 := one.

Definition word_of_bool (b : bool) : word := if b then w1 else w0.

Coercion word_of_bool : bool >-> word.

(* mask made of the bits [n] to [n+k] *)
Fixpoint masks_aux (n k : nat) : Z :=
  match k with
    | O => two_power_nat n
    | S k' => two_power_nat n + masks_aux (S n) k'
  end.

(* mask made of the bits [n] to [n+(p-n)] (p>=n) *)
Definition masks (p n : nat) : word := repr (masks_aux n (p-n)).
Definition anti_masks p n := not (masks p n).

(* mask made of bit [n] *)
Definition mask n := masks n n.
Definition anti_mask n := anti_masks n n.

(* w[p:n] = bits [p] to [n] of [w] (p>=n) *)
Definition bits (p n : nat) (w : word) : word := and (masks p n) w.
Notation "w [ p # n ]" := (bits p n w) (at level 8).

(* value of w[p:n] *)
(*IMPROVE: use a shift instead*)
Definition bits_val (p n : nat) (w : word) : Z := w[p#n] / two_power_nat n.
Definition bits_val_impr (p n : nat) (w : word) : Z := 
  shr w[p#n] (repr (Z_of_nat n)).

(* w[n] = bit [n] of [w] *)
Definition bit n := bits n n.
Notation get := bit.
Notation "w [ n ]" := (bit n w) (at level 8).

(* tell if bit [k] of [w] is set to 1 *)
Definition is_set (n : nat) (w : word) : bool := zne w[n] 0.

(* tell if a signed word is negative *)
Definition is_neg := is_set 31.

(* set w[k] to 1 *)
Definition set (n : nat) (w : word) : word := or (mask n) w.

(* set w[k] to 0 *)
Definition clear (n : nat) (w : word) : word := and (anti_mask n) w.

(* update w[k] *)
Definition update_bit_aux (n : nat) (b : bool) (w : word) : word :=
  if b then clear n w else set n w.
Definition update_bit (n : nat) (v w : word) : word :=
  update_bit_aux n (zeq v 0) w.

(* replace w[p:p-k] by v[k:0] *)
Fixpoint update_bits_aux (p k : nat) (v w : word) : word :=
  match k with
    | O => update_bit p v[0] w
    | S k' => update_bits_aux (pred p) k' v (update_bit p v[k] w)
  end.

(* replace w[p:n] by v[p-n:0] (p>=n) *)
Definition update_bits (p n : nat) (v w : word) : word :=
  update_bits_aux p (p-n) v w.

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

Definition byte_size := 8%nat.
Definition byte := bitvec byte_size.
Definition mk_byte := mk_bitvec byte_size.

Definition get_byte_0 w := mk_byte (intval w[7#0]).
Definition get_byte_1 w := mk_byte (intval w[15#8]).
Definition get_byte_2 w := mk_byte (intval w[23#16]).
Definition get_byte_3 w := mk_byte (intval w[31#24]).

Definition halfword_size := 16%nat.
Definition halfword := bitvec halfword_size.
Definition mk_halfword := mk_bitvec halfword_size.

Definition get_half_0 w := mk_halfword (intval w[15#0]).
Definition get_half_1 w := mk_halfword (intval w[31#16]).

(****************************************************************************)
(** Addresses (p. 68) *)
(****************************************************************************)

Definition address_size := 30%nat.
Definition address := bitvec address_size.
Definition mk_address := mk_bitvec address_size.
Definition address_eqdec := @bitvec_eqdec address_size.

(*IMPROVE: can be improved by using build_bitvec instead of mk_bitvec
since [bits_val 2 31 w] is always smaller than [two_power_nat 30]*)
Definition address_of_word (w : word) : address :=
  mk_address (bits_val 2 31 w).

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
since [bits_val k (k+3) w] is always smaller than [two_power_nat 4]*)
Definition regnum_from_bit (k : nat) (w : word) : regnum :=
  mk_regnum (bits_val k (k+3) w).

(****************************************************************************)
(** some word constants *)
(****************************************************************************)

Definition maxu : word := repr max_unsigned.
Definition max : word := repr max_signed.
Definition min : word := repr min_signed.

Definition w2 : word := repr 2.
Definition w3 : word := repr 3.
Definition w4 : word := repr 4.
Definition w8 : word := repr 8.
Definition w12 : word := repr 12.
Definition w14 : word := repr 14.
Definition w15 : word := repr 15.
Definition w16 : word := repr 16.
Definition w31 : word := repr 31.
Definition w32 : word := repr 32.

(*FIXME: define a function for converting hexadecimal strings into words *)
Definition w0xFFFFFFFF : word := repr max_unsigned.
Definition w0xFFFFFFFE : word := sub maxu w1.
Definition w0xFFFFFFFC : word := sub maxu w3.
Definition w0x00000000 : word := w0.
Definition w0x000000FF : word := repr 255.
Definition w0x0000FF00 : word := repr 65280.
Definition w0x00FF0000 : word := repr 16711680.
Definition w0xFF000000 : word := repr 4278190080.
Definition w0x80000000 : word := repr 2147483648.
Definition w0xFFFF0008 : word := repr 4294901768.
Definition w0x00000008 : word := w8.
Definition w0x00FF00FF : word := repr 16711935.
Definition w0x0000FFFF : word := repr 65535.
Definition w0xFFFF000C : word := repr 4294901772.
Definition w0x0000000C : word := w12.

Definition w0x0000 : halfword := get_half_0 w0.
Definition w0xFFFF : halfword := get_half_0 w0x0000FFFF.
