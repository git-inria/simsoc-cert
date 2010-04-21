(**
SimSoC-Cert, a Coq library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Chapter B3 - The System Control Coprocessor (p. 683)
*)

Set Implicit Arguments.

Require Import Bitvec.

Record state : Type := mk_state {
  (* registers *)
  reg : regnum -> word;
  (* memory *)
  mem : address -> word
}.
