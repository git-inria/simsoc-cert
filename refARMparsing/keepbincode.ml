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
ocamlc -pp camlp4o
*)

(* For testing *)
let rec list_of_stream = parser
  | [< 'x; l = list_of_stream >] -> x :: l
  | [< >] -> []


(* Identifiers *)
let ident =
  let bu = Buffer.create 16 in 
  let rec ident_aux = parser
    | [< '  'a'..'z'| 'A'..'Z' | '0'..'9' as c; s >] -> 
        Buffer.add_char bu c; ident_aux s
    | [< >] -> Buffer.contents bu in
  let ident c s = Buffer.clear bu; Buffer.add_char bu c; ident_aux s in
  ident

(* Returns full line as string *)
let take_eol =
  let bu = Buffer.create 80 in 
  let rec aux = parser
    | [< ''\n' >] -> Buffer.contents bu
    | [< 'c; s >] -> Buffer.add_char bu c; aux s in
  let take_eol c s = Buffer.clear bu; Buffer.add_char bu c; aux s in
  take_eol

exception Empty_line_expected
let skip_empty_line = parser
    | [< ''\n' >] -> ()
    | [<  >] -> raise Empty_line_expected

(* integers *)

let valdigit c = int_of_char c - int_of_char '0'
let rec horner n = parser 
  | [< '  '0'..'9' as c; s >] -> horner (10 * n + valdigit c) s
  | [< >] -> n

(* Jumps to eol *)
let rec eat_eol = parser 
  | [< ''\n'; s >] -> ()
  | [< 'c; s >] -> eat_eol s

(* Reading a header *)
exception Not_header

let rec seqint1 = parser 
  | [< ''0'..'9'as c; n = horner (valdigit c); l = seqint  >] -> n, l
  | [< >] -> raise Not_header
and seqint = parser
  | [< ''.' ; s  >] -> let n, l = seqint1 s in n :: l
  | [< >] -> []

let rec title = parser 
  | [< '' ' ; s >] -> title s
  | [< ''A'..'Z' | 'a'..'z' as c; s = take_eol c >] -> s
  | [< >] -> raise Not_header

(* ex. A4.1.2 ADC  *)
type header = Header of char * int * int list * string

(* In case of failure we want the contents of the line *)
(* SH = Some Header, NH = No Header *)
type opt_header = SH of header | NH of string

let print_header = function
  | Header (c, n, l, s) -> 
    begin
      print_char c;
      print_int n;
      List.iter (Printf.printf ".%i") l ; print_char ' ';
      print_endline s
    end

let end_header c = parser
  | [< n, l = seqint1; t = title >] -> Header (c, n, l, t)

let rec blanks_alpha = parser
  | [< '' ' ; s >] -> blanks_alpha s
  | [< ''A'..'Z' as c; s >] -> 
      try SH (end_header c s )
      with Not_header -> NH (take_eol c s) 

(* A capital alpha at the very beginning of the line *)
let beg_alpha = parser
  | [< ''A'..'Z' as c; s >] -> 
      try SH (end_header c s )
      with Not_header -> NH (take_eol c s) 


exception PB_to_next_header

let rec to_next_header = parser
  | [< ho = beg_alpha; s >] ->
    (match ho with
      | NH _ -> to_next_header s
      | SH h -> h)
  | [< () = eat_eol; s >] -> to_next_header s
  | [< >] -> raise PB_to_next_header

(* Goes after the next header h which satisfies f h and returns h *)
let rec to_given_header f = parser
  | [< h = to_next_header; s >] -> if f h then h else to_given_header f s

(* Strings used for locating the beginning of interesting parts *)
let alpha = "Alphabetical list of ARM instructions"
let alphathumb = "Alphabetical list of Thumb instructions"
let genotes = "General notes"
let addrmodes = "Addressing Mode "
let beforeopdescr = "Shifted register operand value"

(* p is a prefix of s *)
let is_pref p s = 
  let l = String.length p in
  l <= String.length s && String.sub s 0 l = p

(* "fil" means filter *)
let filtitle t0 (Header (c, n, l, t)) =  t = t0
let filpart_kbc c0 (Header (c, n, l, t)) =   c = c0 && List.length l >= 2
let filendinstr (Header (c, n, l, t)) =  List.length l = 1

let preftitle t0 (Header (c, n, l, t)) =  is_pref t0 t

let to_next_Ainstr = to_given_header (filpart_kbc 'A')

let copy_line = parser
  | [< 'c; a = take_eol c >] -> print_endline a

let rec copy_consecutive_lines n s =
  if n = 0 then () 
  else begin copy_line s; copy_consecutive_lines (n-1) s end

(* *)

let in_bincode s = 
   copy_line s; skip_empty_line s; copy_line s

(* Only part A is considered in ARM manual *)


let rec loop_instrs = parser
  | [< h = to_next_header; s >] -> 
      if filpart_kbc 'A' h then
	begin
	  print_header h;
	  in_bincode s;
	  loop_instrs s
	end
      else ()

let main = parser 
    [< _ = to_given_header (filtitle alpha);
       _ = to_given_header (filtitle genotes);
       () = loop_instrs;
       _ = to_given_header (preftitle addrmodes);
       (* 5 consecutive sections to analyze *)
       () = loop_instrs;
       () = loop_instrs;
       () = loop_instrs;
       () = loop_instrs;
       () = loop_instrs;
       _ = to_given_header (filtitle alphathumb);
       _ = to_given_header (filtitle genotes);
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
