(**
SimSoC-Cert, a Coq library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Selection of binary encoding of instructions in the ARM manual, txt format
*)

(* 
#load "dynlink.cma";; 
#load "camlp4o.cma";; 
#load "librap.cmo";;
ocamlc -pp camlp4o
*)

module LR = Librap

(* Strings used for locating the beginning of interesting parts *)
let alpha = "Alphabetical list of ARM instructions"
let alphathumb = "Alphabetical list of Thumb instructions"
let genotes = "General notes"
let addrmodes = "Addressing Mode "
let beforeopdescr = "Shifted register operand value"


let to_next_Ainstr = LR.to_given_header (LR.filpart_kbc 'A')

let copy_line = parser
  | [< 'c; a = LR.take_eol c >] -> print_endline a

let rec copy_consecutive_lines n s =
  if n = 0 then () 
  else begin copy_line s; copy_consecutive_lines (n-1) s end

(* *)

let in_bincode s = 
   copy_line s; LR.skip_empty_line s; copy_line s

(* Only part A is considered in ARM manual *)


let rec loop_instrs = parser
  | [< h = LR.to_next_header; s >] -> 
      if LR.filpart_kbc 'A' h then
	begin
	  LR.print_header h;
	  in_bincode s;
	  loop_instrs s
	end
      else ()

let main = parser 
    [< _ = LR.to_given_header (LR.filtitle alpha);
       _ = LR.to_given_header (LR.filtitle genotes);
       () = loop_instrs;
       _ = LR.to_given_header (LR.preftitle addrmodes);
       (* 5 consecutive sections to analyze *)
       () = loop_instrs;
       () = loop_instrs;
       () = loop_instrs;
       () = loop_instrs;
       () = loop_instrs;
       _ = LR.to_given_header (LR.filtitle alphathumb);
       _ = LR.to_given_header (LR.filtitle genotes);
       () = loop_instrs;
    >]
  -> ()

let () = main (Stream.of_channel stdin)

(*

let cin = open_in "ARMv6.txt"

let cin = open_in "ADC.txt"

let s = Stream.of_channel cin
let test = to_given_header (filtitle alpha) s
let test = to_given_header (filtitle genotes) s
let test = loop_instrs s
let () = close_in cin

let bidon = 0


*)
