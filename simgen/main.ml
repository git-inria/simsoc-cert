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
(** usage and exit function in case of error *)
(*****************************************************************************)

let usage_msg = "usage: " ^ Sys.argv.(0) ^ " option ...\n";;

let error s = error (sprintf "%s\n%s" s usage_msg);;

(*****************************************************************************)
(** functions for setting parameters *)
(*****************************************************************************)

let get_norm, set_norm = get_set_bool();;
let get_check, set_check = get_set_bool();;
let get_sh4, set_sh4 = get_set_bool ()
let get_ml, set_ml = get_set_bool();;

let set_debug() =
  ignore(Parsing.set_trace true); set_debug(); set_verbose();;

let set_check() = set_check(); set_verbose();;

type output_type = PCout | Cxx | C4dt | CoqInst | CoqDec | MlDec
                   | DecBinTest | DecAsmTest | DecTest
                   | RawCoq_Csyntax | CompcertCInst;;

let is_set_pc_input_file, get_pc_input_file, set_pc_input_file =
  is_set_get_set "input file name for pseudocode instructions" "";;

let is_set_dec_input_file, get_dec_input_file, set_dec_input_file =
  is_set_get_set "input file name for decoding instructions" "";;

let is_set_syntax_input_file, get_syntax_input_file, set_syntax_input_file =
  is_set_get_set "input file name for syntax instructions" "";;

let is_set_output_type, get_output_type, set_output_type =
  is_set_get_set "output type" PCout;;

let is_set_output_file, get_output_file, set_output_file =
  is_set_get_set "output file" "";;

let is_set_weight_file, get_weight_file, set_weight_file =
  is_set_get_set "weight file" "";;

let is_set_seed, get_seed, set_seed =
  is_set_get_set "test generator seed" 0;;

let is_set_coqcl_argv, get_coqcl_argv, set_coqcl_argv = 
  is_set_get_set "coq argv" [||]

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
  "-isyntax", String (fun s -> set_syntax_input_file s),
  " Take syntax instructions as input";
  "-iw", String (fun s -> set_weight_file s),
  " Take an additional weight file as input (requires -oc4dt)";
  "-sh4", Unit set_sh4,
  " Assume that we are importing a SH4 data (default is ARM)";
  "-check", Unit set_check,
  " Check pseudocode pretty-printer (only with -ipc)";
  "-norm", Unit set_norm,
  " Normalize pseudocode (only with -ipc)";
  "-ml", Unit set_ml,
  " Use a pure ML algorithm instead of Coq, if possible";
  "-opc", Unit (fun () -> set_output_type PCout),
  " Output pseudocode";
  "-ocxx", String (fun s -> set_norm(); set_output_type Cxx; set_output_file s),
  " Output C (implies -norm, requires -ipc and -idec)";
  "-oc4dt", String (fun s -> set_norm(); set_output_type C4dt; set_output_file s),
  " Output C/C++ for dynamic translation (implies -norm, requires -ipc, -isyntax, and -idec)";
  "-ocoq-inst", Unit (fun () -> set_norm(); set_output_type CoqInst),
  " Output instructions in Coq (implies -norm, requires -ipc)";
  "-ocompcertc-inst", Unit (fun () -> set_norm(); set_output_type CompcertCInst),
  " Output instructions in CompCert C ast (raw Coq syntax) (implies -norm, requires -ipc)";
  "-ocompcertc-c", Rest (fun _ -> if is_set_coqcl_argv () then () else
      let is_set_ml = ref true in
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
                          ; "-ml", (fun x -> let () = is_set_ml := false in x) ]);
        (if !is_set_ml then set_ml () else ());
        set_output_type RawCoq_Csyntax;
      end),
  " Output C program in CompCert C ast (raw Coq syntax) (requires the same options as CompCert)";
  "-ocoq-dec", Unit (fun () -> set_output_type CoqDec),
  " Output Coq decoder (requires -idec)";
  "-oml-dec", Unit (fun () -> set_output_type MlDec),
  " Output Ocaml decoder (requires -idec)";
  "-obin-test", Unit (fun () -> set_norm(); set_output_type DecBinTest),
  " Output test for Coq and Simlight decoders, in binary format (requires -ipc, -isyntax, and -idec)";
  "-s", Int (fun i -> set_seed i),
  " Set the seed to initialize the test generator";
  "-oasm-test", String (fun s -> set_norm(); set_output_type DecAsmTest; set_output_file s),
  " Output test for Coq and Simlight decoders, in assembly format (requires -ipc, -isyntax, and -idec)";
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
    | Cxx -> ignore(get_pc_input_file()); ignore(get_dec_input_file())
    | C4dt ->
        ignore(get_pc_input_file());
        ignore(get_syntax_input_file());
        ignore(get_dec_input_file())
    | CoqInst ->
        if is_set_dec_input_file() then
          error "option -ocoq-inst incompatible with -idec"
        else ignore(get_pc_input_file())
    | CompcertCInst ->
        if is_set_dec_input_file() then
          error "option -ocoq-inst incompatible with -idec"
        else ignore(get_pc_input_file())
    | RawCoq_Csyntax -> ()
    | CoqDec ->
        if is_set_pc_input_file() then
          error "option -ocoq-dec incompatible with -ipc"
        else ignore (get_dec_input_file())
    | MlDec ->
        if is_set_pc_input_file() then
          error "option -oml-dec incompatible with -ipc"
        else ignore (get_dec_input_file())
    | DecBinTest ->
        ignore(get_pc_input_file());
        ignore(get_syntax_input_file());
        ignore(get_dec_input_file())
    | DecAsmTest ->
        ignore(get_pc_input_file());
        ignore(get_syntax_input_file());
        ignore(get_dec_input_file())
    | DecTest ->
        ignore(get_pc_input_file());
        ignore(get_syntax_input_file());
        ignore(get_dec_input_file())
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

(*****************************************************************************)
(** main procedure *)
(*****************************************************************************)

let get_pc_input, set_pc_input = get_set { Ast.header = []; Ast.body = [] };;
let get_dec_input, set_dec_input = get_set [];;
let get_syntax_input, set_syntax_input = get_set [];;
let get_pc_input_cl, set_pc_input_cl = 
  get_set { Ast.header = []; Ast.body = [] };;

let check() =
  if get_check() then
    let ps = get_pc_input() in
    let b = Buffer.create 10000 in
      verbose "reparsing... ";
      Genpc.lib b ps;
      let ps' = parse_string (Buffer.contents b) in
        if ps.Ast.body = ps' then verbose "ok\n" else error "failed";;

let norm split_msr_code =
  if get_norm() then
    let ps = get_pc_input() in
      verbose "normalization... ";
      let ps = Norm.prog (split_msr_code ps) in
        if get_check() then
          let ps' = Norm.prog ps in
            if ps = ps' then verbose "ok\n" else error "failed"
        else verbose "\n";
        set_pc_input ps;
        if is_set_syntax_input_file() then
          let ss = get_syntax_input() in
          let ss' = Norm.split_msr_syntax ss in
            set_syntax_input ss';
            check();;

let parse_input_file() =
  let verbose s = verbose (sprintf (format_of_string s) (if get_sh4 () then "SH4" else "ARM")) in
  let input_bin fic = 
    let ic = open_in_bin fic in
    let v = input_value ic in
    let () = close_in ic in
    v in
  if is_set_syntax_input_file() then (
    verbose "read %s syntax data...\n";
    set_syntax_input (input_bin (get_syntax_input_file()))
  );
  if is_set_pc_input_file() then (
    verbose "parsing %s pseudo-code...\n";

    let input_file = get_pc_input_file () in
    let split_msr_code, pc =
      if get_sh4 () then
        (fun x -> let () = Norm.ref_boolean_not := Norm.bitwise_not in x), 
        C2pc.program_of_manual (let open Manual in (input_bin input_file : raw_c_code manual))
      else
        Norm.split_msr_code, { Ast.header = [] ; Ast.body = parse_file input_file } in

    set_pc_input pc;
    check();
    norm split_msr_code
  );
  if is_set_dec_input_file() then (
    verbose "read %s coding tables...\n";

    set_dec_input 
      (let v = (if get_sh4 () then 
          fun x -> C2pc.maplist_of_manual (input_bin x) 
        else
          input_bin) (get_dec_input_file()) in
       let () = ignore v in
       v)
  );;

let genr_output() =
  verbose "code generation...\n";
  let print_csyntax c = 
    Buffer.output_buffer stdout 
      ((if get_ml () then 
          Csyntax2coq.to_buffer
        else
          RawCoq_Csyntax_main.to_buffer) c) in
  match get_output_type() with
    | PCout -> print Genpc.lib (get_pc_input())
    | Cxx -> Gencxx.lib (get_output_file()) (get_pc_input()) (get_dec_input())
    | C4dt ->
        let wf = if is_set_weight_file() then Some (get_weight_file ()) else None in
          Simlight2.lib (get_output_file()) (get_pc_input())
            (get_syntax_input()) (get_dec_input()) wf
    | CoqInst -> print (Gencoq.lib (if get_sh4 () then
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
    | CoqDec -> print (let open Dec in
                       let module D = Gencoqdec.Make ((val (
                         if get_sh4 () then
                           (module Sh4 : DEC) 
                         else
                           (module Arm : DEC)) : DEC)) in
                       D.decode) (get_dec_input())
    | MlDec -> print Genmldec.decode (get_dec_input())
    | DecBinTest ->
        Gendectest.gen_bin_test stdout (get_pc_input()) (get_syntax_input())
          (get_dec_input()) (get_seed ())
    | DecAsmTest ->
        Gendectest.gen_asm_test (get_output_file()) (get_pc_input()) 
          (get_syntax_input()) (get_dec_input()) (get_seed ())
    | DecTest -> Gendectest.gen_test (get_output_file()) (get_pc_input()) 
          (get_syntax_input()) (get_dec_input()) (get_seed ())
;;

let main() =
  parse_args();
  parse_input_file();
  genr_output();;

(*****************************************************************************)
(** launch the main procedure *)
(*****************************************************************************)

let _ = main();;
