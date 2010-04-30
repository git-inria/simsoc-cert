(**
SimSoC-Cert, a library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Pseudocode compiler.
*)

open Printf;;
open Util;;
open Arg;;
open Lexing;;

(***********************************************************************)
(** usage and exit function in case of error *)
(***********************************************************************)

let usage_msg = "usage: " ^ Sys.argv.(0) ^ " option ...\n";;

let error s = error (sprintf "%s\n%s" s usage_msg);;

(***********************************************************************)
(** functions for setting parameters *)
(***********************************************************************)

let get_norm, set_norm = get_set_bool();;
let get_check, set_check = get_set_bool();;

let set_debug() =
  ignore(Parsing.set_trace true); set_debug(); set_verbose();;

let set_check() = set_check(); set_verbose();;

type input_type = PCin | Decode;;
type output_type = PCout | Cxx | Coq;;

let is_set_input_type, get_input_type, set_input_type =
  is_set_get_set "input type" PCin;;

let is_set_input_file, get_input_file, set_input_file =
  is_set_get_set "input file name" "";;

let is_set_output_type, get_output_type, set_output_type =
  is_set_get_set "output type" PCout;;

(***********************************************************************)
(** command line parsing *)
(***********************************************************************)

let rec options() =
  List.sort (fun (x,_,_) (y,_,_) -> Pervasives.compare x y) (Arg.align
[
  "-h", Unit print_help,
  " Display this list of options";
  "-d", Unit set_debug,
  " Debugging mode";
  "-ipc", String (fun s -> set_input_type PCin; set_input_file s),
  " Take pseudocode instructions as input";
  "-idec", String (fun s -> set_input_type Decode; set_input_file s),
  " Take decoding instructions as input";
  "-check", Unit set_check,
  " Check pseudocode pretty-printer (only with -ipc)";
  "-norm", Unit set_norm,
  " Normalize pseudocode (only with -ipc)";
  "-opc", Unit (fun () -> set_output_type PCout),
  " Output pseudocode";
  "-ocxx", Unit (fun () -> set_output_type Cxx),
  " Output C++";
  "-ocoq", Unit (fun () -> set_norm(); set_output_type Coq),
  " Output Coq (implies -norm)";
  "-v", Unit set_verbose,
  " Verbose mode"
])

and print_options oc =
  List.iter (fun (k, _, d) -> fprintf oc "%s: %s\n" k d) (options())

and print_help() = print_endline usage_msg; print_options stdout; exit 0;;

let options = options();;

let anon_fun _ = error "invalid option";;

let parse_args() =
  Arg.parse options anon_fun usage_msg;
  let _ = get_input_type() in
  let _ = get_input_file() in
  let _ = get_output_type() in
    ();;

(***********************************************************************)
(** parsing functions *)
(***********************************************************************)

let fprint_loc oc loc =
  if loc.pos_fname <> "" then
    fprintf oc "file \"%s\", " loc.pos_fname;
  fprintf oc "line %d, character %d"
    loc.pos_lnum (loc.pos_cnum - loc.pos_bol + 1);;

let parse_lexbuf lb =
  try Parser.lib Lexer.token lb
  with Parsing.Parse_error ->
    fprintf stderr "syntax error: %a\n" fprint_loc lb.lex_curr_p; exit 1;;

let parse_channel ic =
  let lb = Lexing.from_channel ic in
    lb.lex_curr_p <- { lb.lex_curr_p with pos_fname = get_input_file() };
    parse_lexbuf lb;;

let parse_string s = parse_lexbuf (Lexing.from_string s);;

let parse_file fn =
  let ic = open_in fn in
  let x = parse_channel ic in
    close_in ic; x;;

(***********************************************************************)
(** main procedure *)
(***********************************************************************)

type input =
  | Prog of Ast.prog list
  | Dec of Codetype.maplist;;

let get_input, set_input = get_set (Prog []);;

let check() =
  if get_check() then
    match get_input() with
      | Prog ps ->
	  let b = Buffer.create 10000 in
	    verbose "reparsing... ";
	    Genpc.lib b ps;
	    let ps' = parse_string (Buffer.contents b) in
	      if ps = ps' then verbose "ok\n" else error "failed"
      | Dec _ -> error "option -check incompatible with -idec";;

let norm() =
  if get_norm() then
    match get_input() with
      | Prog ps ->
	  verbose "normalization... ";
	  let ps = List.map Norm.prog ps in
	    if get_check() then
	      let ps' = List.map Norm.prog ps in
		if ps = ps' then verbose "ok\n" else error "failed"
	    else verbose "\n";
	    set_input (Prog ps);
	    check();
      | Dec _ -> error "option -norm incompatible with -idec";;

let parse_input_file() =
  verbose "parsing...\n";
  match get_input_type() with
    | PCin ->
	set_input (Prog (parse_file (get_input_file())));
	check();
	norm()
    | Decode -> set_input (Dec (input_value (open_in (get_input_file()))));;

let prog() =
  match get_output_type() with
    | PCout -> Genpc.lib
    | Cxx -> Gencxx.lib
    | Coq -> Gencoq.lib;;

let dec() =
  match get_output_type() with
    | PCout -> error "option -opc incompatible with -idec"
    | Cxx -> error "option -ocxx not yet supported with -idec"
    | Coq -> Gencoqdec.decode;;

let genr_output() =
  verbose "code generation...\n";
  match get_input() with
    | Prog x -> print (prog()) x
    | Dec x -> print (dec()) x;;

let main() =
  parse_args();
  parse_input_file();
  genr_output();;

(***********************************************************************)
(** launch the main procedure *)
(***********************************************************************)

let _ = main();;
