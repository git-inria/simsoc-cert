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

let notspecial c = match c with
  | '<' | '>' | '{' | '}' | '+' | '\n' -> false
  | _ -> true

(* vanilla strings, prefixed by a string and delimited by special characters *)
let string =
  let bu = Buffer.create 16 in 
  let rec string_aux = parser
    | [< 'c when notspecial c; s >] -> Buffer.add_char bu c; string_aux s
    | [< >] -> Buffer.contents bu in
  let string prf s = Buffer.clear bu; Buffer.add_string bu prf; string_aux s in
  string

exception Lacking_char_at_pos of char * int
let endparam = parser
  | [< '  '>' >] -> ()
  | [< s >] -> raise (Lacking_char_at_pos('>', Stream.count s))
let endopt = parser
  | [< '  '}' >] -> ()
  | [< s >] -> raise (Lacking_char_at_pos('}', Stream.count s))


let param = parser
  | [< '  '0'..'9' | 'a'..'z'| 'A'..'Z' | '_' | '!' as c;
       id = LR.ident c;
       () = endparam >] -> id

let plusminus1 = parser
  | [< ''-' >] ->  ST.PlusMinus
  | [< s >] -> ST.Const(string "+/" s)

let plusminus = parser
  | [< ''/' ; r = plusminus1 >] ->  r
  | [< s >] -> ST.Const(string "+" s)

let optparam = parser
  | [< ''<' ; p = param >] -> Some(p)
  | [< >] -> None

 
let token = parser
  | [< ''<' ; p = param >] -> ST.Param(p)
  | [< ''+' ; r = plusminus >] -> r
  | [< ''{' ; c = string ""; o = optparam ; () = endopt >] -> ST.OptParam(c,o)
  | [< s >] -> ST.Const(string "" s)


(* *)

let rec variant = parser
   | [< ''\n' >] -> []
   | [< t = token ; v = variant >] -> t :: v

let rec variants = parser
   | [< '' ' ; v = variant ; vs = variants >] -> v :: vs
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
