(**
SimSoC-Cert, a toolkit for generating certified processor simulators.

See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Enumerated type for used strings for turning extraction problems.
*)

Inductive message : Type :=
| EmptyMessage : message
| ImpreciseDataAbort : message
| InvalidInstructionSet : message
| JazelleInstructionSetNotImplemented : message
| ThumbInstructionSetNotImplemented : message
| DecodingReturnsUnpredictable : message
| StartOpcodeExecutionAt : message
| While : message
| Coproc : message
| Affect : message
| Case : message
| ComplexSemantics : message
| NotAnAddressingMode1 : message
| NotAnAddressingMode2 : message
| NotAnAddressingMode3 : message
| NotAnAddressingMode4 : message
| NotAnAddressingMode5 : message.
