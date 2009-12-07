(**
SimSoC-Cert, a library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Pseudocode compiler.
*)

open Ast;;
open Lexing;;
open Printf;;
open Parsing;;
open Arg;;

let usage_msg () = "usage: " ^ Sys.argv.(0) ^ " [-h|...] file.pc";;

let print_usage_and_exit () = prerr_endline (usage_msg()); exit 1;;

let error s = fprintf stderr "error: %s\n" s; print_usage_and_exit ();;

let get_filename, set_filename =
  let filename = ref "" in
    (fun () -> !filename),
    (fun s -> if !filename = "" then filename := s
     else error "wrong number of arguments");;

let set_debug_mode () = let _ = Parsing.set_trace true in ();;

let rec options () = [
  "-h", Unit print_help, "display the list of options";
  "-d", Unit set_debug_mode, "turn on debug mode";
]

and print_options oc () =
  List.iter (fun (k, _, d) -> fprintf oc "%s: %s\n" k d) (options ())

and print_help () =
  print_endline (usage_msg()); print_options stdout (); exit 0;;

let parse_args () =
  Arg.parse (options()) set_filename (usage_msg());
  if get_filename() = "" then error "no filename given";;

let fprint_loc oc loc =
  Printf.fprintf oc "file \"%s\", line %d, character %d" 
    loc.pos_fname loc.pos_lnum (loc.pos_cnum - loc.pos_bol + 1);;

let open_file fn =
  try open_in fn with Sys_error s -> prerr_endline s; exit 1;;

let parse_file parse fn =
  let ic = open_file fn in
  let x = parse ic in
    close_in ic; x;;

let parse ic =
  let lb = Lexing.from_channel ic in
    lb.lex_curr_p <- { lb.lex_curr_p with pos_fname = get_filename() };
    try Parser.lib Lexer.token lb
    with Parse_error ->
      fprintf stderr "%a: syntax error\n" fprint_loc lb.lex_curr_p; exit 1;;

let main () =
  parse_args ();
  let ps = parse_file parse (get_filename()) in
  let b = Buffer.create 10000 in
    List.iter (Ast.prog b) ps;
    print_endline (Buffer.contents b);;

let _ = main ();;
