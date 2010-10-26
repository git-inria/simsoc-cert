(**
SimSoC-Cert, a Coq library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Parser for binary encoding of instructions
*)

type pos_contents =
  | Nothing
  | Value of bool                  (* false -> 0, true -> 1 *)
  | Param1 of char                 (* e.g. S *)
  | Param1s of string              (* e.g. mmod *)
  | Range of string * int * int    (* length position, e.g. Rn 4 0 *)
  | Shouldbe of bool               (* false -> SBZ, true -> SBO *)

type maplist_element = (Librap.lightheader * pos_contents array)
type maplist = maplist_element list
