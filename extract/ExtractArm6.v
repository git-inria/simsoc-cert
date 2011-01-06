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

Require arm6dec.
Extract Constant arm6dec.decode_addr_mode1 => "Arm6mldec.decode_addr_mode1". 
Extract Constant arm6dec.decode_addr_mode2 => "Arm6mldec.decode_addr_mode2". 
Extract Constant arm6dec.decode_addr_mode3 => "Arm6mldec.decode_addr_mode3". 
Extract Constant arm6dec.decode_addr_mode4 => "Arm6mldec.decode_addr_mode4". 
Extract Constant arm6dec.decode_addr_mode5 => "Arm6mldec.decode_addr_mode5". 
Extract Constant arm6dec.decode_unconditional => "Arm6mldec.decode_unconditional".
Extract Constant arm6dec.decode_conditional => "Arm6mldec.decode_conditional".
Extract Constant arm6dec.decode => "Arm6mldec.decode".


Require Simul.
Require Semantics.
Require ZArith.
Require Functions.

Extraction NoInline Simul.decode_cond.
Extraction NoInline Simul.DecUndefined.
Extraction NoInline Simul.decode_cond_mode.
Extraction NoInline Semantics.if_CurrentModeHasSPSR.
(*Extraction NoInline Semantics.if_then.*)
(*Extraction NoInline andb.*)

(*Print Extraction Inline.*)


Require Extraction arm6.
Recursive Extraction Library arm6.
