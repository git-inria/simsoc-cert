(**
SimSoC-Cert, a toolkit for generating certified processor simulators
See the COPYRIGHTS and LICENSE files.

   Main program.
*)

open Printf;;
open Util;;
open Arg;;
open Lexing;;

(*****************************************************************************)
(** exit function in case of error *)
(*****************************************************************************)

let error s = error (sprintf "%s\n" s);;

(*****************************************************************************)
(** functions for setting parameters *)
(*****************************************************************************)

let get_norm, set_norm = get_set_bool();;
let get_check, set_check = get_set_bool();;
let get_sh4, set_sh4 = get_set_bool ()
let get_coq, set_coq = get_set_bool();;

let set_debug() = ignore(Parsing.set_trace true); set_debug(); set_verbose();;

let set_check() = set_check(); set_verbose();;

type output_type =
  | PCout | Cxx | C4dt | CoqInst | CoqDec | MlDec | DecBinTest | DecAsmTest
  | DecTest | RawCoq_Csyntax | CompcertCInst;;

let is_set_pc_input_file, get_pc_input_file, set_pc_input_file =
  is_set_get_set "input file name for -ipc option" "";;

let is_set_dec_input_file, get_dec_input_file, set_dec_input_file =
  is_set_get_set "input file name for -idec option" "";;

let is_set_syntax_input_file, get_syntax_input_file, set_syntax_input_file =
  is_set_get_set "input file name for -isyntax option" "";;

let is_set_output_type, get_output_type, set_output_type =
  is_set_get_set "output type" PCout;;

let is_set_output_file, get_output_file, set_output_file =
  is_set_get_set "output file" "";;

let is_set_weight_file, get_weight_file, set_weight_file =
  is_set_get_set "weight file" "";;

let is_set_seed, get_seed, set_seed =
  is_set_get_set "test generator seed" 0;;

(*****************************************************************************)
(** compcert options *)
(*****************************************************************************)

let is_set_coqcl_argv, get_coqcl_argv, set_coqcl_argv = 
  is_set_get_set "coq argv" [||]

let ocompcert _ =
  if is_set_coqcl_argv () then () else
      let is_set_coq = ref true in
      begin 
        set_coqcl_argv (List.fold_left
                          (fun argv -> 
                            let find name = (** find the name of the option in [argv], return his index if found *)
                              let rec aux n = 
                                if n < 0 then
                                  None
                                else if argv.(n) = name then
                                  Some n
                                else
                                  aux (pred n) in 
                              aux in
                            fun (name, f_none) -> 
                              let lg = pred (Array.length argv) in
                              match find name lg with
                                | None -> f_none argv
                                | Some p -> (** delete the index found *)
                                  Array.append (Array.sub argv 0 p) (Array.sub argv (succ p) (lg - p)))
                          Sys.argv
                          [ "-ocompcertc-c", (fun _ -> assert false)
                          ; "-coq", (fun x -> let () = is_set_coq := false in x) ]);
        (if !is_set_coq then set_coq () else ());
        set_output_type RawCoq_Csyntax;
      end;;

(*****************************************************************************)
(** parsing command line options and arguments *)
(*****************************************************************************)

let rec options() =
  List.sort (fun (x,_,_) (y,_,_) -> Pervasives.compare x y) ((*Arg.align*)
[
  "-h", Unit print_help,
  ": display this list of options";
  "-d", Unit set_debug,
  ": debugging mode";
  "-ipc", String (fun s -> set_pc_input_file s),
  "file.pc : takes as input a text file with the ARM pseudocode of various instructions";
  "-idec", String (fun s -> set_dec_input_file s),
  "file.dec (.dat with -sh4) : take as input a data file containing an OCaml value of type Codetype.maplist (Manual.manual with -sh4) describing the binary decoding tables of various instructions";
  "-isyntax", String (fun s -> set_syntax_input_file s),
  "file.syntax : takes as input a data file containing an OCaml value of type Syntaxtype.syntax describing the assembly syntax of various instructions";
  "-iwgt", String (fun s -> set_weight_file s),
  "file.wgt : takes as input a weight file (in conjonction with -oc4dt only)";
  "-sh4", Unit set_sh4,
  ": generates code for simulating SH4 (default is ARMv6)";
  "-check", Unit set_check,
  ": check the pseudocode pretty-printer and normalizer (in conjunction with -ipc or -norm only)";
  "-norm", Unit set_norm,
  ": normalize the pseudocode (in conjunction with -ipc only)";
  "-coq", Unit set_coq,
  ": use algorithms extracted from some Coq code whenever possible";
  "-opc", Unit (fun () -> set_output_type PCout),
  ": output on the stdout pseudocode (in conjunction with -ipc only)";
  "-ocxx", String (fun s -> set_norm(); set_output_type Cxx; set_output_file s),
  "prefix : generate various C files implementing a simulator (in conjunction with -ipc and -idec) (implies -norm)";
  "-oc4dt", String (fun s -> set_norm(); set_output_type C4dt; set_output_file s),
  "prefix : generate various C/C++ files implementing a simulator with dynamic translation (in conjonction with -ipc, -isyntax and -idec) (implies -norm)";
  "-ocoq-inst", Unit (fun () -> set_norm(); set_output_type CoqInst),
  ": output on stdout Coq code defining the semantics of instructions (in conjunction with -ipc) (implies -norm)";
  "-ocompcertc-inst", Unit (fun () -> set_norm(); set_output_type CompcertCInst),
  ": output on stdout Coq code representing some CompCert-C code representing the pseudocode given in input (in conjonction with -ipc only) (implies -norm)";
  "-ocompcertc-c", Rest ocompcert,
  "file.c : output on stdout Coq code representing the C code given in input using the CompCert library";
  "-ocoq-dec", Unit (fun () -> set_output_type CoqDec),
  ": output on stdout Coq code for decoding instructions (in conjunction with -idec only)";
  "-oml-dec", Unit (fun () -> set_output_type MlDec),
  ": output on stdout Ocaml code for decoding instructions (in conjunction with -idec only)";
  "-obin-test", Unit (fun () -> set_norm(); set_output_type DecBinTest),
  ": output binary code (without ELF header) to test instruction decoders (in conjunction with -ipc, -isyntax and -idec only)";
  "-seed", Int (fun i -> set_seed i),
  "integer : set the seed of the pseudo-random number generator used to generate tests";
  "-oasm-test", String (fun s -> set_norm(); set_output_type DecAsmTest; set_output_file s),
  "file.asm : generate assembly code to test decoders (in conjunction with -ipc, -isyntax and -idec only)";
  "-v", Unit set_verbose,
  ": verbose mode"
])

and print_options oc =
  fprintf oc "options:\n";
  List.iter (fun (k, _, d) -> fprintf oc "  %s %s\n" k d) (options())

and print_help() = print_options stdout; exit 0;;

let options = options();;

let anon_fun _ = error "unknown option";;

(* parse command line arguments and verify that the right input files
   are provided *)

let parse_args() =
  Arg.parse options anon_fun "options:";
  match get_output_type() with
    | PCout ->
	ignore (get_pc_input_file());
    | Cxx ->
	ignore (get_pc_input_file());
	ignore (get_dec_input_file())
    | C4dt ->
        ignore (get_pc_input_file());
        ignore (get_syntax_input_file());
        ignore (get_dec_input_file())
    | CoqInst ->
        ignore (get_pc_input_file())
    | CompcertCInst ->
        ignore (get_pc_input_file())
    | RawCoq_Csyntax ->
	()
    | CoqDec ->
        ignore (get_dec_input_file())
    | MlDec ->
        ignore (get_dec_input_file())
    | DecBinTest ->
        ignore (get_pc_input_file());
        ignore (get_syntax_input_file());
        ignore (get_dec_input_file())
    | DecAsmTest ->
        ignore (get_pc_input_file());
        ignore (get_syntax_input_file());
        ignore (get_dec_input_file())
    | DecTest ->
        ignore (get_pc_input_file());
        ignore (get_syntax_input_file());
        ignore (get_dec_input_file())
;;

(*****************************************************************************)
(** parsing pseudocode or ocaml values *)
(*****************************************************************************)

let fprint_loc oc loc =
  if loc.pos_fname <> "" then
    fprintf oc "file \"%s\", " loc.pos_fname;
  fprintf oc "line %d, character %d"
    loc.pos_lnum (loc.pos_cnum - loc.pos_bol + 1);;

let parse_lexbuf lb =
  try Parser.lib Lexer.token lb
  with Parsing.Parse_error ->
    let () = eprintf "syntax error: %a\n%!" fprint_loc lb.lex_curr_p in
    exit 1;;

let parse_channel ic =
  let lb = Lexing.from_channel ic in
    lb.lex_curr_p <- { lb.lex_curr_p with pos_fname = get_pc_input_file() };
    parse_lexbuf lb;;

let parse_string s = parse_lexbuf (Lexing.from_string s);;

let parse_file fn =
  let ic = open_in fn in
  let x = parse_channel ic in
    close_in ic; x;;

let parse_value fn = 
  let ic = open_in_bin fn in
  let v = input_value ic in
    close_in ic; v

(*****************************************************************************)
(** functions for setting input data *)
(*****************************************************************************)

let get_pc_input, set_pc_input = get_set { Ast.header = []; Ast.body = [] };;
let get_dec_input, set_dec_input = get_set [];;
let get_syntax_input, set_syntax_input = get_set [];;

(*****************************************************************************)
(** check pseudocode pretty-printer (-check option) *)
(*****************************************************************************)

let check() =
  if get_check() then
    let ps = get_pc_input() in
    let b = Buffer.create 10000 in
      verbose "reparsing... ";
      Genpc.lib b ps;
      let ps' = parse_string (Buffer.contents b) in
        if ps.Ast.body = ps' then verbose "ok\n" else error "failed";;

(*****************************************************************************)
(** pseudocode normalization (-norm option) *)
(*****************************************************************************)

let norm _split_msr_code =
  if get_norm() then begin
    verbose "normalization... ";
    let ps = get_pc_input() in
    let ps = Norm.prog ((*split_msr_code*) ps) in
      if get_check() then
        let ps' = Norm.prog ps in
          if ps = ps' then verbose "ok\n" else error "failed"
      else verbose "\n";
      set_pc_input ps(*(*why setting syntax_input?*);
      if is_set_syntax_input_file() then
        let ss = get_syntax_input() in
        let ss' = Norm.split_msr_syntax ss in
          set_syntax_input ss';
          check()(*why calling check again here?*)*)
  end;;

(*****************************************************************************)
(** set input data by parsing input files *)
(*****************************************************************************)

let parse_input_files() =
  let verbose s = verbose (sprintf (format_of_string s)
			     (if get_sh4() then "Sh4" else "Arm6")) in
  if is_set_syntax_input_file() then (
    verbose "read %s syntax data...\n";
    set_syntax_input (parse_value (get_syntax_input_file()))
  );
  if is_set_pc_input_file() then (
    verbose "parsing %s pseudocode...\n";
    let split_msr_code, pc =
      if get_sh4() then
        (fun x -> let () = Norm.ref_boolean_not := Norm.bitwise_not in x),
        C2pc.program_of_manual
	  (let open Manual in (parse_value (get_pc_input_file()) : raw_c_code manual))
      else
        Norm.split_msr_code,
        { Ast.header = []; Ast.body = parse_file (get_pc_input_file()) }
    in
      set_pc_input pc;
      check();
      norm split_msr_code
  );
  if is_set_dec_input_file() then (
    verbose "read %s coding tables...\n";
    set_dec_input
      (let v = parse_value (get_dec_input_file()) in
	 if get_sh4() then C2pc.maplist_of_manual v else v)
  );;

(*****************************************************************************)
(** generate outputs *)
(*****************************************************************************)

let genr_output() =
  verbose "code generation...\n";
  let print_csyntax c = 
    Buffer.output_buffer stdout 
      ((if get_coq () then 
          RawCoq_Csyntax_main.to_buffer
        else
          Csyntax2coq.to_buffer) c) in
  match get_output_type() with

    | PCout ->
	print Genpc.lib (get_pc_input())

    | Cxx ->
	Gencxx.lib (get_output_file()) (get_pc_input()) (get_dec_input())

    | C4dt ->
        Simlight2.lib (get_output_file())
	  (get_pc_input()) (get_syntax_input()) (get_dec_input())
	  (if is_set_weight_file() then Some (get_weight_file()) else None)

    | CoqInst -> print (Gencoq.lib (if get_sh4() then
        (module struct
          let nb_buff = 0
          let preamble_name = "Sh4_"
          let preamble_comment = "SH4"
          let preamble_proc = "Sh4"
          let preamble_import = "Sh4_Functions."
        end : Gencoq.GENCOQ)
      else
        (module struct
          let nb_buff = 5
          let preamble_name = "Arm6_"
          let preamble_comment = "ARMv6 addressing modes and"
          let preamble_proc = "Arm6 Arm6_SCC"
          let preamble_import = "State Arm6_Functions."
        end : Gencoq.GENCOQ))) (get_pc_input())

    | CompcertCInst -> 
      print_csyntax (Pc2Csyntax.prog_trans (get_pc_input()))

    | RawCoq_Csyntax -> 
      let open CompCert_Driver in
      (match main (module struct let argv = get_coqcl_argv () end : SYS) with
        | None -> Printf.printf "(* assert false *)\n%!"
        | Some b -> print_csyntax b)

    | CoqDec ->
	print (let open Dec in
               let module D = Gencoqdec.Make ((val (
                         if get_sh4 () then
                           (module Sh4 : DEC) 
                         else
                           (module Arm : DEC)) : DEC)) in
                       D.decode) (get_dec_input())

    | MlDec ->
	print Genmldec.decode (get_dec_input())

    | DecBinTest ->
        Gendectest.gen_bin_test stdout (get_pc_input()) (get_syntax_input())
          (get_dec_input()) (get_seed())

    | DecAsmTest ->
        Gendectest.gen_asm_test (get_output_file()) (get_pc_input()) 
          (get_syntax_input()) (get_dec_input()) (get_seed())

    | DecTest ->
	Gendectest.gen_test (get_output_file()) (get_pc_input()) 
          (get_syntax_input()) (get_dec_input()) (get_seed())
;;

let main() =
  parse_args();
  parse_input_files();
  genr_output();;

(*****************************************************************************)
(** launch the main procedure *)
(*****************************************************************************)

let _ = main();;
