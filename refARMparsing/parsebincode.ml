(**
SimSoC-Cert, a Coq library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Parser for binary encoding of instructions
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
let ident, ident2 =
  let bu = Buffer.create 16 in 
  let rec ident_aux = parser
    | [< '  'a'..'z'| 'A'..'Z' | '0'..'9' | '_' as c; s >] -> 
        Buffer.add_char bu c; ident_aux s
    | [< >] -> Buffer.contents bu in
  let ident c s = Buffer.clear bu; Buffer.add_char bu c; ident_aux s in
  let ident2 c0 c1 s =
    Buffer.clear bu; Buffer.add_char bu c0; Buffer.add_char bu c1; ident_aux s in
  ident, ident2

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

(* Sequence of integers separated by 1 dot *)
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

let end_header c = parser
  | [< n, l = seqint1; t = title >] -> Header (c, n, l, t)


let rec header = parser
  | [< '' ' ; s >] -> header s
  | [< ''A'..'Z' as c; s >] -> end_header c s

(* Sequence of integers separated by white spaces *)
exception Not_seq_int_spaces
let rec seqwhint1 c = parser 
  | [< n = horner (valdigit c); l = seqwhint  >] -> n :: l
  | [< >] -> raise Not_seq_int_spaces
and seqwhint = parser
  | [< '' ' ; s  >] -> seqwhint s
  | [< ''0'..'9'as c; s  >] -> seqwhint1 c s
  | [< >] -> []

type token = 
  Zero | One | Char of char | String of string

let rec char_or_string c0 = parser
  | [< '  'a'..'z'| 'A'..'Z' | '0'..'9' | '_' as c1; s >] -> 
      String (ident2 c0 c1 s)
  | [< >] -> Char (c0)


let rec token = parser
  | [< '' ' ; s >] -> token s
  | [< ''0' >] -> Zero
  | [< ''1' >] -> One
  | [< '  'a'..'z'| 'A'..'Z' | '_' as c; s >] -> char_or_string c s

let rec seq_tokens = parser
  | [< t = token; l = seq_tokens >] -> t :: l
  | [< >] -> []

type operation = Operation of header * int list * token list

let operation = parser
  | [< h = header;
       li = seqwhint;
       () = skip_empty_line;
       lc = seq_tokens;
       () = skip_empty_line
    >] -> Operation (h, li, lc)


let cin = open_in "ADCbin.txt"
let s = Stream.of_channel cin
let test = operation s
let () = close_in cin


(* GARBAGE *)


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
    >]
  -> ()

let () = main (Stream.of_channel stdin)

(*

let cin = open_in "ARMv6.txt"

let cin = open_in "ADCbin.txt"

let s = Stream.of_channel cin
let test = to_given_header (filtitle alpha) s
let test = to_given_header (filtitle genotes) s
let test = loop_instrs s
let () = close_in cin

let bidon = 0


*)
