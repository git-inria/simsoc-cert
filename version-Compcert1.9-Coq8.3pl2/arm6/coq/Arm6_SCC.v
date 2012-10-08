(**
SimSoC-Cert, a toolkit for generating certified processor simulators.

See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Chapter B3 - The System Control Coprocessor (p. 683)
*)

Set Implicit Arguments.

Require Import Coqlib Bitvec Util.

(****************************************************************************)
(** B3.4.1 Control register (p. 694) *)
(****************************************************************************)

Definition Mbit := 0%nat.
Definition Abit := 1%nat.
Definition Wbit := 3%nat.
Definition Vbit := 13%nat.
Definition Ubit := 22%nat.
Definition VEbit := 24%nat.
Definition EEbit := 25%nat.

(****************************************************************************)
(** Coprocessor state *)
(****************************************************************************)

Record state : Type := mk_state {
  (* registers *)
  reg : regnum -> word;
  (* memory *)
  mem : address -> word
}.

Definition CP15_reg1 (s : state) : word := reg s (mk_regnum 1).

Definition high_vectors_configured (s : state) : bool :=
  is_set Vbit (CP15_reg1 s).

(* FIXME: the code below simulates little endian memory *)
Definition first_bit (a: word) :=
  nat_of_Z (unsigned (mul (repr 8) (bits 1 0 a))).


Definition read_bits (n : size) (a w : word) :=
  match n with
    | Word => w
    | Half => let f := first_bit a in bits (f+15) f w
    | Byte => let f := first_bit a in bits (f+7) f w
  end.

Definition read (s : state) (a : word) (n : size) : word :=
  read_bits n a (mem s (address_of_word a)).

(* a: address; v: new value; v: old value *)
Definition write_bits (n : size) (a v w : word) :=
  match n with
    | Word => v
    | Half => let f := first_bit a in set_bits (f+15) f v w
    | Byte => let f := first_bit a in set_bits (f+7) f v w
  end.

Definition write (s : state) (a : word) (n : size) (v : word) : state :=
  let aa := address_of_word a in
  mk_state (reg s)
  (update_map Address.eq_dec (mem s) aa (write_bits n a v (mem s aa))).
