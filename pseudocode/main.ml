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

let usage_msg () = "usage: " ^ Sys.argv.(0) ^ " [option] [file]";;

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

type action = GenPC | GenPCCheck | GenPre | GenCxx | GenCoq | GenCoqDec;;

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
  "-h", Unit print_help, " Display this list of options";
  "-d", Unit set_debug_mode, " Turn on debug mode";
  "-pc", Unit (fun () -> set_action GenPC), " Generate pseudocode";
  "-pc-check", Unit (fun () -> set_action GenPCCheck),
  " Generate pseudocode and reparse it";
  "-norm", Unit (fun () -> set_action GenPre),
  " Generate normalized pseudocode";
  "-cxx", Unit (fun () -> set_action GenCxx), " Generate instructions in C++";
  "-coq", Unit (fun () -> set_action GenCoq), " Generate instructions in Coq";
  "-coq-decoder", Unit (fun () -> set_action GenCoqDec),
  " Generate decoder in Coq";
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

let parse_lexbuf lb =
  try Parser.lib Lexer.token lb
  with Parsing.Parse_error ->
    fprintf stderr "%a: syntax error\n" fprint_loc lb.lex_curr_p; exit 1;;

let parse_channel ic =
  let lb = Lexing.from_channel ic in
    lb.lex_curr_p <- { lb.lex_curr_p with pos_fname = get_filename() };
    parse_lexbuf lb;;

let parse_string s = parse_lexbuf (Lexing.from_string s);;

let parse_file fn =
  let ic = open_in fn in
  let x = parse_channel ic in
    close_in ic; x;;

(***********************************************************************)
(** main procedure *)
(***********************************************************************)

let print f x =
  let b = Buffer.create 10000 in
    f b x; Buffer.output_buffer stdout b;;

let output gen = print gen (parse_file (get_filename()));;

let output_norm gen =
  print gen (List.map Preproc.prog (parse_file (get_filename())));;

let genpc_check () =
  let b = Buffer.create 10000 in
  let ps = parse_file (get_filename()) in
    Genpc.lib b ps;
    Buffer.output_buffer stdout b;
    let ps' = parse_string (Buffer.contents b) in
      fprintf stderr "reparsing: %s\n"
	(if ps = ps' then "good" else "wrong");;

let main () =
  parse_args ();
  match get_action () with
    | GenCoqDec ->
	print Gencoqdec.decode (input_value (open_in (get_filename ())))
    | GenPC -> output Genpc.lib
    | GenPCCheck -> genpc_check ()
    | GenPre -> output_norm Genpc.lib
    | GenCxx -> output_norm Gencxx.lib
    | GenCoq -> output_norm Gencoq.lib;;

(***********************************************************************)
(** launch the main procedure *)
(***********************************************************************)

let _ = main ();;
