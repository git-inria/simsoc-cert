(**
SimSoC-Cert, a toolkit for generating certified processor simulators
See the COPYRIGHTS and LICENSE files.

   Data structure for representing the binary encoding of processor
   instructions.
*)

type pos_contents =
  | Nothing
  | Value of bool                  (* false -> 0, true -> 1 *)
  | Param1 of char                 (* e.g. S *)
  | Param1s of string              (* e.g. mmod *)
  | Range of string * int * int    (* length position, e.g. Rn 4 0 *)
  | Shouldbe of bool               (* false -> SBZ, true -> SBO *)

type maplist_element = (Lightheadertype.lightheader * pos_contents array)
type maplist = maplist_element list
