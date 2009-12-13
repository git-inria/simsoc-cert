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

type op = Char of char | String of string | Nop

(* Full line *)
let take_eol =
  let bu = Buffer.create 80 in 
  let rec deb op = parser
    | [< ''\n' >] -> op, Buffer.contents bu
    | [< '' '; s >] -> Buffer.add_char bu ' '; deb op s
    | [< ''+' | '-' as c; s >] -> Buffer.clear bu; fin (Char c) s 
    | [< '  'a'..'z' | 'A'..'Z' as c; s >] -> let i = ident c s in 
      (match i with
	 | "or" | "and" | "OR" | "AND"  as op -> Buffer.clear bu; fin (String op) s 
	 | _ -> Buffer.add_string bu i; fin op s
      )
    | [< 'c; s >] -> Buffer.add_char bu c; fin op s 
  and fin op  = parser
    | [< ''\n' >] -> op, Buffer.contents bu
    | [< 'c; s >] -> Buffer.add_char bu c; fin op s in
  let take_eol c s = Buffer.clear bu; Buffer.add_char bu c; deb Nop s in
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
