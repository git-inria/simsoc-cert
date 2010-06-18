type lightheader = LH of int list * string
(* the int list contains always two elements:
 * - the first is the section number:
     o always 1 for instructions
     o for addressing modes, it is the addressing mopde number (from 1 to 5)
 * - the second is the instruction number or the addressing mode case number 
 * NB: the chapter number is not given 
 *)

type pos_contents = 
  | Nothing
  | Value of bool                  (* false -> 0, true -> 1 *)
  | Param1 of char                 (* e.g. S *)
  | Param1s of string              (* e.g. mmod *)
  | Range of string * int * int    (* length position, e.g. Rn 4 0 *)
  | Shouldbe of bool               (* false -> SBZ, true -> SBO *)

type maplist_element = (lightheader * pos_contents array)
type maplist = maplist_element list
