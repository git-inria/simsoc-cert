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

(*****************************************************************************)
(** usage and exit function in case of error *)
(*****************************************************************************)

let usage_msg = "usage: " ^ Sys.argv.(0) ^ " option ...\n";;

let error s = error (sprintf "%s\n%s" s usage_msg);;

(*****************************************************************************)
(** functions for setting parameters *)
(*****************************************************************************)

let get_norm, set_norm = get_set_bool();;
let get_check, set_check = get_set_bool();;

let set_debug() =
  ignore(Parsing.set_trace true); set_debug(); set_verbose();;

let set_check() = set_check(); set_verbose();;

type output_type = PCout | Cxx | C4dt | CoqInst | CoqDec | DecTest;;

let is_set_pc_input_file, get_pc_input_file, set_pc_input_file =
  is_set_get_set "input file name for pseudocode instructions" "";;

let is_set_dec_input_file, get_dec_input_file, set_dec_input_file =
  is_set_get_set "input file name for decoding instructions" "";;

let is_set_output_type, get_output_type, set_output_type =
  is_set_get_set "output type" PCout;;

let is_set_output_file, get_output_file, set_output_file =
  is_set_get_set "output file" "";;

let is_set_weight_file, get_weight_file, set_weight_file =
  is_set_get_set "weight file" "";;

let is_set_seed, get_seed, set_seed =
  is_set_get_set "test generator seed" 0;;

(*****************************************************************************)
(** command line parsing *)
(*****************************************************************************)

let rec options() =
  List.sort (fun (x,_,_) (y,_,_) -> Pervasives.compare x y) (Arg.align
[
  "-h", Unit print_help,
  " Display this list of options";
  "-d", Unit set_debug,
  " Debugging mode";
  "-ipc", String (fun s -> set_pc_input_file s),
  " Take pseudocode instructions as input";
  "-idec", String (fun s -> set_dec_input_file s),
  " Take decoding instructions as input";
  "-iw", String (fun s -> set_weight_file s),
  " Take an additional weight file as input (requires -oc4dt)";
  "-check", Unit set_check,
  " Check pseudocode pretty-printer (only with -ipc)";
  "-norm", Unit set_norm,
  " Normalize pseudocode (only with -ipc)";
  "-opc", Unit (fun () -> set_output_type PCout),
  " Output pseudocode";
  "-ocxx", String (fun s -> set_norm(); set_output_type Cxx; set_output_file s),
  " Output C (implies -norm, requires -ipc and -idec)";
  "-oc4dt", String (fun s -> set_norm(); set_output_type C4dt; set_output_file s),
  " Output C/C++ for dynamic translation (implies -norm, requires -ipc and -idec)";
  "-ocoq-inst", Unit (fun () -> set_norm(); set_output_type CoqInst),
  " Output Coq instructions (implies -norm, requires -ipc)";
  "-ocoq-dec", Unit (fun () -> set_output_type CoqDec),
  " Output Coq decoder (requires -idec)";
  "-otest", Unit (fun () -> set_norm(); set_output_type DecTest),
  " Output test for Coq and Simlight decoders, in binary format (requires -idec)";
  "-s", Int (fun i -> set_seed i),
  " Set the seed to initialize the test generator";
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
  (* Verify that the right input files are provided *)
  match get_output_type() with
    | PCout ->
        if is_set_dec_input_file() then
          error "option -opc incompatible with -idec"
        else ignore(get_pc_input_file());
    | Cxx | C4dt -> ignore(get_pc_input_file());  ignore(get_dec_input_file())
    | CoqInst ->
        if is_set_dec_input_file() then
          error "option -ocoq-inst incompatible with -idec"
        else ignore(get_pc_input_file())
    | CoqDec ->
        if is_set_pc_input_file() then
          error "option -ocoq-dec incompatible with -ipc"
        else ignore (get_dec_input_file())
    | DecTest ->
	ignore(get_pc_input_file()); ignore (get_dec_input_file())
;;

(*****************************************************************************)
(** parsing functions *)
(*****************************************************************************)

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
    lb.lex_curr_p <- { lb.lex_curr_p with pos_fname = get_pc_input_file() };
    parse_lexbuf lb;;

let parse_string s = parse_lexbuf (Lexing.from_string s);;

let parse_file fn =
  let ic = open_in fn in
  let x = parse_channel ic in
    close_in ic; x;;

(*****************************************************************************)
(** main procedure *)
(*****************************************************************************)

let get_pc_input, set_pc_input = get_set [];;
let get_dec_input, set_dec_input = get_set [];;

let check() =
  if get_check() then
    let ps = get_pc_input() in
    let b = Buffer.create 10000 in
      verbose "reparsing... ";
      Genpc.lib b ps;
      let ps' = parse_string (Buffer.contents b) in
	if ps = ps' then verbose "ok\n" else error "failed";;

let norm() =
  if get_norm() then
    let ps = get_pc_input() in
      verbose "normalization... ";
      let ps = List.map Norm.prog (Norm.split_msr ps) in
	if get_check() then
	  let ps' = List.map Norm.prog ps in
	    if ps = ps' then verbose "ok\n" else error "failed"
	else verbose "\n";
	set_pc_input ps;
	check();;

let parse_input_file() =
  verbose "parsing...\n";
  if is_set_pc_input_file() then (
    set_pc_input (parse_file (get_pc_input_file()));
    check();
    norm());
  if is_set_dec_input_file() then
    set_dec_input (input_value (open_in (get_dec_input_file())));;

let genr_output() =
  verbose "code generation...\n";
  match get_output_type() with
    | PCout -> print Genpc.lib (get_pc_input())
    | Cxx -> Gencxx.lib (get_output_file()) (get_pc_input()) (get_dec_input())
    | C4dt ->
        let wf = if is_set_weight_file() then Some (get_weight_file ()) else None in
          Simlight2.lib (get_output_file()) (get_pc_input()) (get_dec_input()) wf
    | CoqInst -> print Gencoq.lib (get_pc_input())
    | CoqDec -> print Gencoqdec.decode (get_dec_input())
    | DecTest -> 
	Gendectest.gen_test stdout (get_pc_input()) (get_dec_input()) (get_seed ());;   

let main() =
  parse_args();
  parse_input_file();
  genr_output();;

(*****************************************************************************)
(** launch the main procedure *)
(*****************************************************************************)

let _ = main();;
