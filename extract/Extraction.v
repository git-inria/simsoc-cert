(**
SimSoC-Cert, a Coq library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Configuration of a ARM processor (IMPLEMENTATION DEFINED parameters).
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

Require arm6.
Recursive Extraction Library arm6.
