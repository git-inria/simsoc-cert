(**
SimSoC-Cert, a Coq library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Chapter B3 - The System Control Coprocessor (p. 683)
*)

Set Implicit Arguments.

Require Import Bitvec Util.

(****************************************************************************)
(** B3.4.1 Control register (p. 694) *)
(****************************************************************************)

Definition Mbit := 0%nat.
Definition Abit := 1%nat.
Definition Wbit := 3%nat.
Definition Ubit := 22%nat.
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

Definition read_bits (n : size) (w : word) :=
  match n with
    | Word => w
    | Half => set_bits 31 16 w0 w (*IMPROVE: use a shift instead*)
    | Byte => set_bits 31 8 w0 w
  end.

Definition read (s : state) (a : address) (n : size) : word :=
  read_bits n (mem s a).

Definition write_bits (n : size) (v w : word) :=
  match n with
    | Word => v
    | Half => set_bits 15 0 v w
    | Byte => set_bits 7 0 v w
  end.

Definition write (s : state) (a : address) (n : size) (v : word) : state :=
  mk_state (reg s)
  (update_map address_eqdec (mem s) a (write_bits n v (mem s a))).
