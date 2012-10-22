(**
SimSoC-Cert, a toolkit for generating certified processor simulators.

See the COPYRIGHTS and LICENSE files.

Extraction of RawCoq_Csyntax.
*)

Require Extraction RawCoq_Csyntax.

Cd "extraction".

(* For Coq-8.4 *)
Recursive Extraction Library Vector.

Extraction Library RawCoq_Csyntax.