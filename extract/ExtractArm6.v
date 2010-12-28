(**
SimSoC-Cert, a Coq library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Extraction of the arm6 simulator.
*)

Require List.

(*Unset Extraction Optimize.*)
(*Unset Extraction AutoInline.*)

Extract Inductive unit => "unit" [ "()" ].
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive option => "option" [ "Some" "None" ].
Extract Inductive List.list => "list" [ "[]" "(::)" ].
 
Require Simul.
Require Semantics.
Require ZArith.

Extraction NoInline Simul.decode_cond.
Extraction NoInline Simul.DecUndefined.
Extraction NoInline Simul.decode_cond_mode.
Extraction NoInline Semantics.if_CurrentModeHasSPSR.
(*Print Extraction Inline.*)


Require Extraction arm6.
Recursive Extraction Library arm6.




