(**
SimSoC-Cert, a Coq library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Global state.
*)

Set Implicit Arguments.

Require Import Proc.
Require Import Bitvec.

(****************************************************************************)
(** A2.7 Endian support (p. 68) *)
(****************************************************************************)

Definition address := bitvec 30.

Definition mk_address := mk_bitvec 30.

Definition address_eqdec := @bitvec_eqdec 30.

(*IMPROVE: can be improved by using build_bitvec instead of mk_bitvec
since [bits_val 2 31 w] is always smaller than [two_power_nat 30]*)
Definition address_of_word (w : word) : address :=
  mk_address (bits_val 2 31 w).

(****************************************************************************)
(** Global state *)
(****************************************************************************)

Record state : Type := mk_state {
  (* Processor *)
  proc : Proc.state;
  (* Memory *)
  mem : address -> word;
  (* System control coprocessor *)
  scc : reg_num -> word
}.
