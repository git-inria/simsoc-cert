(**
SimSoC-Cert, a library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Pseudocode compiler.
*)

open Printf;;
open Arg;;
open Lexing;;

(***********************************************************************)
(** usage and exit function in case of error *)
(***********************************************************************)

let usage_msg () = "usage: " ^ Sys.argv.(0) ^ " [-h|...] (-pc) file";;

let print_usage_and_exit () = prerr_endline (usage_msg()); exit 1;;

let error s = fprintf stderr "error: %s\n" s; print_usage_and_exit ();;

(***********************************************************************)
(** parameters *)
(***********************************************************************)

let get_filename, set_filename =
  let filename = ref "" in
    (fun () -> !filename),
    (fun s -> if !filename = "" then filename := s
     else error "wrong number of arguments");;

let set_debug_mode () = let _ = Parsing.set_trace true in ();;

type action = Gen_PC | Gen_PCC;;

let get_action, is_action_set, set_action =
  let action = ref Gen_PC and is_set = ref false in
    (fun () -> !action),
    (fun () -> !is_set),
    (fun a -> if !is_set then error "wrong number of options"
     else begin action := a; is_set := true end);;

(***********************************************************************)
(** command line parsing *)
(***********************************************************************)

let rec options () = [
  "-h", Unit print_help, "display the list of options";
  "-d", Unit set_debug_mode, "turn on debug mode";
  "-pc", Unit (fun () -> set_action Gen_PC), "generate pseudocode";
  "-pcc", Unit (fun () -> set_action Gen_PCC),
  "generate pseudocode and reparse it";
]

and print_options oc () =
  List.iter (fun (k, _, d) -> fprintf oc "%s: %s\n" k d) (options ())

and print_help () =
  print_endline (usage_msg()); print_options stdout (); exit 0;;

let parse_args () =
  Arg.parse (options()) set_filename (usage_msg());
  if get_filename() = "" then error "no filename given";
  if not (is_action_set()) then error "wrong number of option";;

(***********************************************************************)
(** parsing functions *)
(***********************************************************************)

let fprint_loc oc loc =
  Printf.fprintf oc "file \"%s\", line %d, character %d" 
    loc.pos_fname loc.pos_lnum (loc.pos_cnum - loc.pos_bol + 1);;

let open_file fn =
  try open_in fn with Sys_error s -> prerr_endline s; exit 1;;

let parse_file parse_channel fn =
  let ic = open_file fn in
  let x = parse_channel ic in
    close_in ic; x;;

let parse_lexbuf lb =
  try Parser.lib Lexer.token lb
  with Parsing.Parse_error ->
    fprintf stderr "%a: syntax error\n" fprint_loc lb.lex_curr_p; exit 1;;

let parse_channel ic =
  let lb = Lexing.from_channel ic in
    lb.lex_curr_p <- { lb.lex_curr_p with pos_fname = get_filename() };
    parse_lexbuf lb;;

let parse_string s =
  let lb = Lexing.from_string s in parse_lexbuf lb;;

(***********************************************************************)
(** main procedure *)
(***********************************************************************)

let string_of f ps =
  let b = Buffer.create 10000 in
    f b ps; Buffer.contents b;;

let main () =
  parse_args ();
  let ps = parse_file parse_channel (get_filename()) in
    match get_action () with
      | Gen_PC ->
	  let s = string_of Genpc.lib ps in
	    print_endline s
      | Gen_PCC ->
	  let s = string_of Genpc.lib ps in
	    print_endline s;
	    let ps' = parse_string s in
	      fprintf stderr "reparsing: %s\n"
		(if ps = ps' then "good" else "wrong");;

(***********************************************************************)
(** launch the main procedure *)
(***********************************************************************)

let _ = main ();;
