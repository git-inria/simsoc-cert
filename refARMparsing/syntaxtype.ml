(**
SimSoC-Cert, a Coq library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Parser for binary encoding of instructions
*)

type token =
  | Param of string (* <string> *)
  | OptParam of string * string option (* {fixed part, optional parameter} *)
  | PlusMinus (* +/- *)
  | Const of string (* all other possibilities *)


type variant = token list
type syntax = Lightheadertype.lightheader (* ref *) * variant list
