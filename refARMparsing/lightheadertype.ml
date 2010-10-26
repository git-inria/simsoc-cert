(**
SimSoC-Cert, a Coq library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

The light header type, used by other files in this directory, and by files
living in the pseudocode directory too.
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
