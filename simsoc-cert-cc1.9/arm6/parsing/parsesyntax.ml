(**
SimSoC-Cert, a Coq library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Parser for syntax of instructions
*)

(* 
#load "syntaxtype.cmo";; 
#load "dynlink.cma";; 
#load "camlp4o.cma";; 
#load "librap.cmo";;
ocamlc -pp camlp4o
*)

module LR = Librap
module ST = Syntaxtype

(* vanilla strings, prefixed by a string and delimited by special characters *)
let notspecial c = match c with
  | '<' | '>' | '{' | '}' | '+' | '\n' -> false
  | _ -> true

let string =
  let bu = Buffer.create 16 in 
  let rec string_aux = parser
    | [< 'c when notspecial c; s >] -> Buffer.add_char bu c; string_aux s
    | [< >] -> Buffer.contents bu in
  let string prf s = Buffer.clear bu; Buffer.add_string bu prf; string_aux s in
  string

(* Consumes an expected character at the current position *)
exception Lacking_char_at_pos of char * int
let endparam = parser
  | [< '  '>' >] -> ()
  | [< s >] -> raise (Lacking_char_at_pos('>', Stream.count s))
let endopt = parser
  | [< '  '}' >] -> ()
  | [< s >] -> raise (Lacking_char_at_pos('}', Stream.count s))


(* Identifier followed by '>' *)
let param = parser
  | [< '  '0'..'9' | 'a'..'z'| 'A'..'Z' | '_' | '!' as c;
       id = LR.ident c;
       () = endparam >] -> id

(* The "+/-" token *)
let plusslash = parser
  | [< ''-' >] ->  ST.PlusMinus
  | [< s >] -> ST.Const(string "+/" s)

let plus = parser
  | [< ''/' ; r = plusslash >] ->  r
  | [< s >] -> ST.Const(string "+" s)

(* Optional parameter *)
let optparam = parser
  | [< ''<' ; p = param >] -> Some(p)
  | [< >] -> None

 
(* *)

let token = parser
  | [< ''<' ; p = param >] -> ST.Param(p)
  | [< ''+' ; r = plus >] -> r
  | [< ''{' ; c = string ""; o = optparam ; () = endopt >] -> ST.OptParam(c,o)
  | [< s >] -> ST.Const(string "" s)


(* *)

(* Utility *)
let rec skip_blancs = parser
   | [< '' ' ; s >] -> skip_blancs s
   | [< >] -> ()


(* *)

(*
Here we assume that a header starts at the very beginning of a line,
whereas variants start with a blank character. 
*)
let rec variant = parser
   | [< ''\n' >] -> []
   | [< t = token ; v = variant >] -> t :: v

let rec variants = parser
   | [< '' ' ; () = skip_blancs; v = variant ; vs = variants >] -> v :: vs
   | [< >] -> []

let instruction = parser
  | [< h = LR.header; vs = variants >] -> LR.light h, vs

(* *)

let rec syntax = parser
  | [< i = instruction; l = syntax >] -> i :: l
  | [< >] -> []

(* *)

let main s : ST.syntax list = syntax s

(* *)

let () =
  let l = main (Stream.of_channel stdin) in
  output_value stdout l

(* test: print the list of headers, so we can check if some instructions are missing *)

(*
module LH = Lightheadertype

let print_lightheader = function
    LH.LH (l, s) ->
      print_int (List.nth l 0); print_char '.';
      print_int (List.nth l 1); print_char '.';
      print_int (List.nth l 2); print_char '\t';
      print_endline s

let () =
  let l = main (Stream.of_channel stdin) in
    List.iter (fun (lh,_) -> print_lightheader lh) l
*)

(* *)

(*

(* tests *)

let () = close_in cin
let cin = open_in "resu_keepsyntax.ref"
let s = Stream.of_channel cin
let i = instruction s
let i = instruction s
let i = instruction s
let i = main s
let _ = Stream.count s

*)
