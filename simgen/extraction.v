(**
SimSoC-Cert, a toolkit for generating certified processor simulators.

See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Extraction of the arm6 simulator.
*)

Require Extraction RawCoq_Csyntax.

Cd "extraction".

(*MOVE to coq/extraction.v:
Extraction Library NaryFunctions.
Extraction Library Bvector.*)
Extraction Library RawCoq_Csyntax.
