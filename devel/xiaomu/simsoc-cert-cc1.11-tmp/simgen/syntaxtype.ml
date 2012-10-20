(**
SimSoC-Cert, a toolkit for generating certified processor simulators
See the COPYRIGHTS and LICENSE files.

Parser for binary encoding of instructions
*)

type token =
  | Param of string (* <string> *)
  | OptParam of string * string option (* {fixed part, optional parameter} *)
  | PlusMinus (* +/- *)
  | Const of string (* all other possibilities *)

type variant = token list

type syntax = Lightheadertype.lightheader (* ref *) * variant list
