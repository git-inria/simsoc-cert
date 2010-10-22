(**
SimSoC-Cert, a Coq library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Put multi line expressions on one line
by detecting lines starting with a binop : +, AND, and, OR, or
*)

(* 
#load "dynlink.cma";; 
#load "camlp4o.cma";; 
#load "librap.cmo";;
ocamlc -pp camlp4o
*)

module LR = Librap

(* For testing *)
let rec list_of_stream = parser
  | [< 'x; l = list_of_stream >] -> x :: l
  | [< >] -> []


type op = Char of char | String of string | Nop

(* Full line *)
(* Different from librap version *)
(* A \n after a bin op is discarded 
   We assume that there are no trailing blanks
*)
let take_eol =
  let bu = Buffer.create 80 in
  let rec header = parser (* header shall not be modified *)
    | [< ''\n' >] -> Nop, Buffer.contents bu
    | [< 'c; s >] -> Buffer.add_char bu c; header s
  and deb op = parser
    | [< ''\n' >] -> op, Buffer.contents bu
    | [< '' '; s >] -> Buffer.add_char bu ' '; deb op s
    | [< ''+' | '-' as c; s >] -> Buffer.clear bu; fin (Char c) s 
    | [< '  'a'..'z' | 'A'..'Z' as c; s >] -> let i = LR.ident c s in 
      (match i with
	 | "or" | "and" | "OR" | "AND"  as op -> Buffer.clear bu; after_op (String op) s 
	 | _ -> Buffer.add_string bu i; fin op s
      )
    | [< 'c; s >] -> Buffer.add_char bu c; fin op s 
  and fin op  = parser
    | [< ''\n' >] -> op, Buffer.contents bu
    | [< ''+' | '-' as c; s >] -> Buffer.add_char bu c; after_op op s 
    | [< '  'a'..'z' | 'A'..'Z' as c; s >] -> let i = LR.ident c s in 
      (Buffer.add_string bu i;
       match i with
	 | "or" | "and" | "OR" | "AND"  -> after_op op s
	 | _ -> fin op s
      )
    | [< 'c; s >] -> Buffer.add_char bu c; fin op s 
  and after_op op = parser
    | [< ''\n'; s >] -> Buffer.add_char bu ' '; eat_blanks op s
    | [< 'c; s >] -> Buffer.add_char bu c; fin op s
  and eat_blanks op = parser
    | [< '' '; s >] -> eat_blanks op s
    | [< 'c; s >] -> Buffer.add_char bu c; fin op s
  in
  let take_eol c s =
    Buffer.clear bu; Buffer.add_char bu c;
    if c = 'A' then header s else deb Nop s in
  take_eol

let rec loop = parser 
  | [< 'c; o, a = take_eol c; s >] -> 
      (match o with
	| Nop -> print_newline ()
	| Char o -> print_char ' '; print_char o
	| String o -> print_char ' '; print_string o
      );
      print_string a; loop s
  | [< >] -> print_newline ()


let main = parser 
  | [< 'c; o, a = take_eol c; s >] -> 
      print_string a; loop s
  | [< >] -> ()

let () = main (Stream.of_channel stdin)

(*

let cin = open_in "petit.txt"
let s = Stream.of_channel cin
let test = main s
let () = close_in cin

let a = 1


*)
