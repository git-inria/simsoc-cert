(**
SimSoC-Cert, a toolkit for generating certified processor simulators
See the COPYRIGHTS and LICENSE files.

*)

type lightheader = LH of int list * string

(* the int list contains always three elements:
 * - the first is the chapter number
     4 -> ARM instruction
     5 -> Addressing mode
     7 -> Thumb instruction
 * - the second is the section number:
     o always 1 for instructions
     o for addressing modes, it is the addressing mode number (from 1 to 5)
 * - the third is the instruction number or the addressing mode case number
*)
