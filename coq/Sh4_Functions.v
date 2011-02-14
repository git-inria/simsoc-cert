(**
SimSoC-Cert, a Coq library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the SH4 architecture following the:

SH-4, Software Manual, Renesas 32-Bit RISC, Rev.6.00 2006.09

Page numbers refer to Renesas_SH4_2006.pdf.

Functions used in the pseudocode.
*)

Set Implicit Arguments.

Require Import Coqlib Util Bitvec Sh4 Integers.

Definition Logical_Shift_Left := shl.
Definition Logical_Shift_Right := shru.