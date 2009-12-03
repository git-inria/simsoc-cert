(**
SimSoC-Cert, a Coq library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Pseudocode syntax and semantics.
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

(* Full line *)
let take_eol =
  let bu = Buffer.create 80 in 
  let rec aux = parser
    | [< ''\n' >] -> Buffer.contents bu
    | [< 'c; s >] -> Buffer.add_char bu c; aux s in
  let take_eol c s = Buffer.clear bu; Buffer.add_char bu c; aux s in
  take_eol

(* integers *)

let valdigit c = int_of_char c - int_of_char '0'
let rec horner n = parser 
  | [< '  '0'..'9' as c; s >] -> horner (10 * n + valdigit c) s
  | [< >] -> n


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


type header = Header of char * int * int list * string

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

let optheader = parser
  | [< ''A'..'Z' as c; s >] -> 
      try Some (end_header c s )
      with Not_header -> let () = eat_eol s in None


let rec to_next_header = parser
  | [< ho = optheader; s >] ->
    (match ho with
      | None -> to_next_header s
      | Some _ -> ho)
  | [< () = eat_eol; s >] -> to_next_header s
  | [< >] -> None

let rec to_given_header f = parser
  | [< ho = to_next_header; s >] ->
    (match ho with
      | None -> raise Not_found
      | Some h -> if f h then h else to_given_header f s)
  | [< >] -> raise Not_found

let alpha = "Alphabetical list of ARM instructions"
let genotes = "General notes"

let filtitle t0 (Header (c, n, l, t)) =  t = t0
let filpart c0 (Header (c, n, l, t)) =   c = c0 && List.length l = 2
let filendinstr (Header (c, n, l, t)) =  List.length l = 1

let to_next_Ainstr = to_given_header (filpart 'A')


let rec to_contents_instr = parser
  | [< '' ' ; s >] -> to_contents_instr s
  | [< ''A'..'Z' as c; a = take_eol c; s >] ->
      if a = "Operation" then ()
      else to_contents_instr s
  | [< () = eat_eol; s >] -> to_contents_instr s

let rec in_op = parser 
  | [< ''\n'; s >] -> in_op1 s
  | [< 'c; a = take_eol c; s >] -> 
    print_endline a; in_op s
and in_op1 = parser 
  | [< ''\n' >] -> ()
  | [< 'c; a = take_eol c; s >] ->
    print_endline a; in_op s

(* Only part A is considered in ARM manual *)
let rec loop_instrs = parser
  | [< ho = to_next_header; s >] -> 
    (match ho with
      | None -> ()
      | Some h ->
	  if filpart 'A' h then 
	    begin
	      print_header h;
	      to_contents_instr s;
	      in_op s;
              loop_instrs s
	    end
	  else if filendinstr h then ()
	  else loop_instrs s)
  | [< >] -> ()

let main = parser 
    [< _ = to_given_header (filtitle alpha);
       _ = to_given_header (filtitle genotes);
       () = loop_instrs >]
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
