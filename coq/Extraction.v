(**
SimSoC-Cert, a toolkit for generating certified processor simulators
See the COPYRIGHTS and LICENSE files.

Extraction parameters.
*)

Extraction Language Ocaml.

Set Extraction Optimize.

Set Extraction AutoInline.

(*Extraction Inline ... .*)

(*Extraction NoInline ... .*)

Extraction Blacklist list string.

(*with coq-svn:
Require ExtrOcamlBasic ExtrOcamlString ExtrOcamlNatInt.*)

(*without coq-svn:*)
Extract Inductive unit => unit [ "()" ].
Extract Inductive bool => bool [ true false ].
Extract Inductive sumbool => bool [ true false ].
Extract Inductive option => option [ Some None ].
Extract Inductive prod => "(*)"  [ "" ]. (* instead of "(,)" *)

Require Import List.
Extract Inductive list => list [ "[]" "(::)" ].
