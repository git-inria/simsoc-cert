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

let usage_msg () = "usage: " ^ Sys.argv.(0) ^ " [-h|...] file";;

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

type action = GenPC | GenPCC | GenPre | GenCxx | GenCoq | GenCoqDec;;

let get_action, is_action_set, set_action =
  let action = ref GenPC and is_set = ref false in
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
  "-pc", Unit (fun () -> set_action GenPC), "generate pseudocode";
  "-pcc", Unit (fun () -> set_action GenPCC),
  "generate pseudocode and reparse it";
  "-pre", Unit (fun () -> set_action GenPre), "generate normalized pseudocode";
  "-cxx", Unit (fun () -> set_action GenCxx), "generate instructions in C++";
  "-coq", Unit (fun () -> set_action GenCoq), "generate instructions in Coq";
  "-coq-decode", Unit (fun () -> set_action GenCoqDec),
  "generate decoder in Coq";
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

let parse_string s = parse_lexbuf (Lexing.from_string s);;

(***********************************************************************)
(** main procedure *)
(***********************************************************************)

let print f x =
  let b = Buffer.create 10000 in
    f b x; Buffer.output_buffer stdout b;;

let genpcc ps =
  let b = Buffer.create 10000 in
    Genpc.lib b ps;
    Buffer.output_buffer stdout b;
    let ps' = parse_string (Buffer.contents b) in
      fprintf stderr "reparsing: %s\n"
	(if ps = ps' then "good" else "wrong");;

let main () =
  parse_args ();
  match get_action () with
    | GenCoqDec -> print Decode.decode (input_value (open_in (get_filename ())))
    | GenPC|GenPCC|GenPre|GenCxx|GenCoq ->
	let ps = parse_file parse_channel (get_filename()) in
	  match get_action () with
	    | GenPC -> print Genpc.lib ps
	    | GenPCC -> genpcc ps
	    | GenPre -> print Genpc.lib (List.map Preproc.prog ps)
	    | GenCxx -> print Gencxx.lib (List.map Preproc.prog ps)
	    | GenCoq -> print Gencoq.lib (List.map Preproc.prog ps)
	    | GenCoqDec -> ();;

(***********************************************************************)
(** launch the main procedure *)
(***********************************************************************)

let _ = main ();;
