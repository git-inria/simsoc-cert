(**
SimSoC-Cert, a toolkit for generating certified processor simulators.

See the COPYRIGHTS and LICENSE files.

Formalization of the SH4 architecture following the:

SH-4, Software Manual, Renesas 32-Bit RISC, Rev.6.00 2006.09

Page numbers refer to Renesas_SH4_2006.pdf.

Enumerated type for used strings for turning extraction problems.
*)

Inductive message : Type :=
| InvalidInstructionSet : message
| DecodingReturnsUnpredictable : message
| ComplexSemantics : message.
