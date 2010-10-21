(**
SimSoC-Cert, a Coq library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Selection of pseudo-code for instructions in the ARM manual, txt format
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


let to_next_Ainstr = LR.to_given_header (LR.filpart 'A')


let rec to_contents_instr = parser
  | [< '' ' ; s >] -> to_contents_instr s
  | [< ''A'..'Z' as c; a = LR.take_eol c; s >] ->
      if a = "Syntax" then ()
      else to_contents_instr s
  | [< () = LR.eat_eol; s >] -> to_contents_instr s

let rec in_operation = parser 
  | [< ''\n'; s >] -> ()
  | [< 'c; a = LR.take_eol c; s >] ->
    print_endline a; in_operation s

(* Only part A is considered in ARM manual *)

type stop_ou_encore = Stop | Continue | Op of LR.header 
exception PB_check_then_to_operation_or_next_header

let rec to_operation_or_next_header h = parser
  | [< ba = LR.blanks_alpha; s >] ->
      (match ba with 
      | LR.NH "Syntax" -> Op h
      | LR.NH _ -> to_operation_or_next_header h s
      | LR.SH h1 -> check_then_to_operation_or_next_header h1 s )
  | [< () = LR.eat_eol; s >] -> to_operation_or_next_header h s
and check_then_to_operation_or_next_header h s = 
      if LR.filpart 'A' h then to_operation_or_next_header h s
      else if LR.filendinstr h then Stop
      else Continue


let rec loop_instrs = parser
  | [< h = LR.to_next_header; s >] -> 
      (match check_then_to_operation_or_next_header h s with
	 | Op h1 -> 
	     begin
	       LR.print_header h1;
	       in_operation s;
               loop_instrs s
	     end
	 | Stop -> ()
	 | Continue -> loop_instrs s
       )

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


*)
