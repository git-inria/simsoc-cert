(**
SimSoC-Cert, a Coq library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the SH4 architecture following the:

SH-4, Software Manual, Renesas 32-Bit RISC, Rev.6.00 2006.09

Page numbers refer to Renesas_SH4_2006.pdf.


*)

type pos = 
  | R (* range *) of int (* pos *) * int (* len *)
  | P (* position *) of int

type contents = All | S of string | Re of string (* regexp *)

type action = 
  | Replace_all of string * string
  | Replace_first of contents * string
  | Replace_tilde of int (* space or context to consider, measured by number of lines *)
  (*| Add_line_bef*)
  | Add_line_aft of string
  | Add_char_beg of string (* beginning of line *)
  | Add_char_end of string (* end of line *)
  | Comment (* replace the lines by a whole comment : /* */ *)

open Printf

let string_of_pos = function
  | R (p, l) -> sprintf "R (%d, %d)" p l
  | P p -> sprintf "P %d" p 

let string_of_contents = function
  | All -> "All"
  | S s -> sprintf "S \"%s\"" (String.escaped s)
  | Re s -> sprintf "Re \"%s\"" (String.escaped s)

let string_of_action = function
  | Replace_all (s1, s2) -> sprintf "Replace_all (\"%s\", \"%s\")" (String.escaped s1) (String.escaped s2)
  | Replace_first (c, s) -> sprintf "Replace_first (%s, \"%s\")" (string_of_contents c) (String.escaped s)
  | Replace_tilde i -> sprintf "Replace_tilde %d" i
  | Add_line_aft s -> sprintf "Add_line_aft \"%s\"" (String.escaped s)
  | Add_char_beg s -> sprintf "Add_char_beg \"%s\"" (String.escaped s)
  | Add_char_end s -> sprintf "Add_char_end \"%s\"" (String.escaped s)
  | Comment -> "Comment" 

