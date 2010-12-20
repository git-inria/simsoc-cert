(**
SimSoC-Cert, a Coq library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Bit vectors, based on Xavier Leroy Compcert.Integers file.

Defines also the following implicit coercions:

regnum, byte, half, address, word > Z
bool > word
nat > regnum > word
byte > word
half > word
address > word
word > long
*)

Set Implicit Arguments.

Require Import Util ZArith Coqlib Integers.
Export Int.

(****************************************************************************)
(** A2.1 Data types (p. 39) *)
(****************************************************************************)

Inductive size : Type := Byte | Half | Word.

(****************************************************************************)
(** 32-bits words, masks and bit operations *)
(****************************************************************************)

Module Word := Int.

Notation word := int.
Notation mk_word := mkint.

Implicit Arguments mkint [intval].

Coercion intval : word >-> Z.

Notation w0 := zero.
Notation w1 := one.

Definition word_of_bool (b : bool) : word := if b then w1 else w0.

Coercion word_of_bool : bool >-> word.

Definition bool_of_word (w: word) : bool := zne w 0.

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

Definition byte0 (w : word) : word := bits 7 0 w.
Definition byte1 (w : word) : word := bits 15 8 w.
Definition byte2 (w : word) : word := bits 23 16 w.
Definition byte3 (w : word) : word := bits 31 24 w.

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
(** convert word to type w32 to make the decoder faster *)
(****************************************************************************)

Require Import NaryFunctions Util.

Inductive w32 : Type := word32 : bool^^32 --> w32.

Definition w32_of_word (w : int) : w32 :=
  nary_iter_decr (bits_of_Z 32 (unsigned w)) 32 31 word32.

Inductive w28 : Type := word28 : bool^^28 --> w28.

Definition w28_of_word (w : int) : w28 :=
  nary_iter_decr (bits_of_Z 28 (unsigned w)) 28 27 word28.

(****************************************************************************)
(** bytes (8-bits words) *)
(****************************************************************************)

Notation mk_byte := Byte.repr.

Coercion Byte.intval : byte >-> Z.

(*FIXME: uncomment when Util.two_power_nat_monotone is proved

Lemma byte_in_range : forall b : byte, 0 <= b < Word.modulus.

Proof.
intros [x h]. simpl. unfold Byte.modulus in h. unfold modulus.
assert (two_power_nat Byte.wordsize <= two_power_nat wordsize).
apply two_power_nat_monotone. omega.
Qed.

Definition word_of_byte (x : byte) : word := mkint (byte_in_range x).*)

Definition word_of_byte (x : byte) : word := repr x.

Coercion word_of_byte : byte >-> word.

Definition get_byte0 w := mk_byte (w[7#0]).
Definition get_byte1 w := mk_byte (w[15#8]).
Definition get_byte2 w := mk_byte (w[23#16]).
Definition get_byte3 w := mk_byte (w[31#24]).

(****************************************************************************)
(** half-words (16-bits words) *)
(****************************************************************************)

Module Wordsize_16.
  Definition wordsize := 16%nat.
  Remark wordsize_not_zero: wordsize <> 0%nat.
  Proof. unfold wordsize; congruence. Qed.
End Wordsize_16.

Module Half := Make(Wordsize_16).

Notation half := Half.int.
Notation mk_half := Half.repr.

Coercion Half.intval : half >-> Z.

(*IMPROVE*)
Definition word_of_half (x : half) : word := repr x.

Coercion word_of_half : half >-> word.

Definition get_half0 w := mk_half (w[15#0]).
Definition get_half1 w := mk_half (w[31#16]).

(****************************************************************************)
(** A2.3 Registers (p. 42) *)
(****************************************************************************)

Module Wordsize_4.
  Definition wordsize := 4%nat.
  Remark wordsize_not_zero: wordsize <> 0%nat.
  Proof. unfold wordsize; congruence. Qed.
End Wordsize_4.

Module Regnum := Make(Wordsize_4).

Notation regnum := Regnum.int.
Notation mk_regnum := Regnum.repr.

Coercion Regnum.intval : regnum >-> Z.

(*IMPROVE*)
Definition word_of_regnum (x : regnum) : word := repr x.

Coercion word_of_regnum : regnum >-> word.

Definition PC := mk_regnum 15.
Definition LR := mk_regnum 14.
Definition SP := mk_regnum 13.

(*IMPROVE: can be improved by using build_bitvec instead of mk_bitvec
since [bits (k+3) k w] is always smaller than [two_power_nat 4]*)
Definition regnum_from_bit (k : nat) (w : word) : regnum :=
  mk_regnum (bits (k+3) k w).

Definition regnum_of_nat (n : nat) : regnum := mk_regnum (Z_of_nat n).

Coercion regnum_of_nat : nat >-> regnum.

(****************************************************************************)
(** Addresses (p. 68) *)
(****************************************************************************)

Module Wordsize_30.
  Definition wordsize := 30%nat.
  Remark wordsize_not_zero: wordsize <> 0%nat.
  Proof. unfold wordsize; congruence. Qed.
End Wordsize_30.

Module Address := Make(Wordsize_30).

Notation address := Address.int.
Notation mk_address := Address.repr.

(*REMOVE: Coercion Address.intval : address >-> Z. *)

(*IMPROVE*)
Definition word_of_address (x : address) : word := repr (Address.intval x).

(*REMOVE: Coercion word_of_address : address >-> word. *)

(*REMOVE:Definition address_eqdec := @bitvec_eqdec address_size.*)

(*IMPROVE: can be improved by using build_bitvec instead of mk_bitvec
since [bits 31 2 w] is always smaller than [two_power_nat 30]*)
Definition address_of_word (w : word) : address := mk_address (bits 31 2 w).

(****************************************************************************)
(** 64-bits words *)
(****************************************************************************)

Module Wordsize_64.
  Definition wordsize := 64%nat.
  Remark wordsize_not_zero: wordsize <> 0%nat.
  Proof. unfold wordsize; congruence. Qed.
End Wordsize_64.

Module Long := Make(Wordsize_64).

Notation long := Long.int.
Notation mk_long := Long.repr.

Coercion Long.intval : long >-> Z.

(*IMPROVE*)
Definition long_of_word (x : word) : long := mk_long x.

Coercion long_of_word : word >-> long.

(* mask made of the bits n to n+(p-n) (p>=n) *)
Definition masks64 (p n : nat) : long := mk_long (masks_aux n (p-n)).

Definition bits_val64 (p n : nat) (w : long) : Z :=
  Long.and (masks64 p n) w / two_power_nat n.

Definition sbits64 (p n : nat) (w : long) : Z := Word.signed (repr (bits_val64 p n w)).

Definition unsbits64 (p n : nat) (w : long) : Z := Word.unsigned (repr (bits_val64 p n w)).

Definition unsigned_mul64 (w1 w2 : word) : long :=
  Long.mul w1 w2.

Definition signed_mul64 (w1 w2 : word) : long :=
  match Word.signed w1, Word.signed w2 with
    | Z0, _ | _, Z0 => mk_long Z0
    | Zpos w1', Zpos w2' | Zneg w1', Zneg w2' => 
      mk_long (Zpos (w1' * w2'))
    | Zpos w1', Zneg w2' | Zneg w1', Zpos w2' =>
      mk_long (Zneg (w1' * w2'))
  end.

Definition bits_of_unsigned_mul64 (w1 w2 : word) (n1 n2 : nat) : word :=
  repr (unsbits64 n1 n2 (unsigned_mul64 w1 w2)).

Definition bits_of_signed_mul64 (w1 w2 : word) (n1 n2 : nat) : word :=
  repr (sbits64 n1 n2 (signed_mul64 w1 w2)).

Definition lt_0 (x: word) : bool :=
  match Word.signed x with
    | Z0 => false
    | Zpos x' => false
    | Zneg x' => true
  end.

Definition n0 := 0%nat.
Definition n1 := (S n0).
Definition n2 := (S n1).
Definition n3 := (S n2).
Definition n4 := (S n3).
Definition n5 := (S n4).
Definition n6 := (S n5).
Definition n7 := (S n6).
Definition n8 := (S n7).
Definition n9 := (S n8).
Definition n10 := (S n9).
Definition n11 := (S n10).
Definition n12 := (S n11).
Definition n13 := (S n12).
Definition n14 := (S n13).
Definition n15 := (S n14).
Definition n16 := (S n15).
Definition n17 := (S n16).
Definition n18 := (S n17).
Definition n19 := (S n18).
Definition n20 := (S n19).
Definition n21 := (S n20).
Definition n22 := (S n21).
Definition n23 := (S n22).
Definition n24 := (S n23).
Definition n25 := (S n24).
Definition n26 := (S n25).
Definition n27 := (S n26).
Definition n28 := (S n27).
Definition n29 := (S n28).
Definition n30 := (S n29).
Definition n31 := (S n30).
Definition n32 := (S n31).
Definition n47 := (S (n23 + n23)).
Definition n63 := (S (n31 + n31)).
