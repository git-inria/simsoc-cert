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

(* Full line, returns: number of leading blanks, contents *)
let take_eol_indent =
  let bu = Buffer.create 80 in 
  (* beginning of line *)
  let rec bol n = parser
    | [< ''\n' >] -> n, Buffer.contents bu
    | [< '' ' as c; s >] -> Buffer.add_char bu c; bol (n+1) s
    | [< s >] -> rol n s
  (* rest of line *)
  and rol n = parser
    | [< ''\n' >] -> n, Buffer.contents bu
    | [< 'c; s >] -> Buffer.add_char bu c; rol n s in
  let take_eol s = Buffer.clear bu; bol 0 s in
  take_eol


(* *)

exception Error of int

let rec prbl n s = if n = 0 then print_endline s else (print_char ' '; prbl (n-1) s)

(* lnb = line number *)
(* n l represents the non-empty stack n :: l of previous indentations *)

let rec unstack lnb n n0 l0 =
  if n >= n0 then n0, l0 (* Should be = but robustness required *)
  else if n < n0 then
    let () = prbl n0 "end" in
    match l0 with 
      | [] -> raise (Error lnb) 
      | n1 :: l1 -> unstack lnb n n1 l1
  else raise (Error lnb) 

type optline = Line of (int * string) | EOL

let rec loop lnb0 n0 l0 s =
  let nc = try Line (take_eol_indent s) with Stream.Failure -> EOL in
  let lnb = lnb0 + 1 in 
  match nc with
    | Line (n, c) -> 
	if n > n0 then (prbl n "begin"; print_endline c; loop lnb n (n0 :: l0) s)
        else let n1, l1 = unstack lnb n n0 l0 in print_endline c; loop lnb n1 l1 s
    | EOL -> let _ = unstack lnb 0 n0 l0 in ()


let () = loop 1 0 [] (Stream.of_channel stdin)
