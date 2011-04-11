(**
SimSoC-Cert, a toolkit for generating certified processor simulators.

See the COPYRIGHTS and LICENSE files.

Extraction of the Arm6 simulator.
*)

Require Extraction Simul.

Cd "extraction".

Extraction Library Bitvec.
Extraction Library Util.
Extraction Library Semantics.
Extraction Library Simul.
Extraction Library NaryFunctions.
Extraction Library Bvector.