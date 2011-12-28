(**
SimSoC-Cert, a Coq library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the SH4 architecture following the:

SH-4, Software Manual, Renesas 32-Bit RISC, Rev.6.00 2006.09

Page numbers refer to Renesas_SH4_2006.pdf.


*)

open Pervasive
open Pdf_page
open Sh4_section
open Manual

module I (C_parse : C_PARSE) = 
struct
  module M = M (C_parse)
  open M

let display_dec = false
let display_c = true

let mk_code l = 
  { init = l
  ; code = C_parse.c_of_program (List.fold_left (Printf.sprintf "%s%s\n") "" l) }

let preprocess_parse_c : string list manual -> raw_c_code manual = fun m -> 
  (** the preprocessing [C_parse.preprocess] function needs to receive a single C file (for replacing all directive variable for example), that is why we concatenate the header and all the instructions *)
  let (pos, code), l_pos =
    List.fold_left (fun ((pos, acc_s), l_pos) l -> 
      List.fold_left (fun (pos, acc_s) s -> succ pos, Printf.sprintf "%s%s\n" acc_s s)
        (pos, acc_s) l, pos :: l_pos) ((0, ""), [])
      (m.entete :: List.map (fun i -> i.c_code) m.section) in

  let _, (_, l, ll) =
    List.fold_left 
      (fun (pos, (l_pos, acc_l, acc_ll)) s -> 
        pred pos, 
        match l_pos with
          | [] -> 
            [], s :: acc_l, acc_ll
          | x :: xs -> 
            if pos = x then
              xs, [s], acc_l :: acc_ll
            else
              l_pos, s :: acc_l, acc_ll) 
      (pos, (l_pos, [], [])) 
      (C_parse.expand_line_space (C_parse.preprocess code)) in

  { entete = mk_code l ; section = List.map2 (fun l i -> { i with c_code = mk_code l }) ll m.section }

let parse_c : string list manual -> raw_c_code manual = fun m -> 
  { entete = mk_code m.entete ; section = List.map (fun i -> { i with c_code = mk_code i.c_code }) m.section }

(** We regroup a line written into a multi-lines into a single block. Heuristic used : we consider as a member of a previous line, any line beginning with a space. *)
(* Remark : we can replace the "Assert_failure" by a "[]" *)
let structure_line = 
  let rec aux l = function 
    | x :: xs -> 
      
      let rec aux2 l_bl = function
        | x :: xs when x.[0] = ' ' -> aux2 (x :: l_bl) xs
        | xs -> List.rev l_bl, xs in
      let l_bl, xs = aux2 [] xs in
      if xs = [] then
        List.rev ((x, l_bl) :: l)
      else
        aux ((x, l_bl) :: l) xs
    | _ -> assert false in
  aux []

(** Simplify a string (only formed with : 0, 1, n, m, i, d) into a list composed of the character and the number of occurences it appears after *)
let list_of_string_01nmid s = 
  let lg = String.length s in
  let () = match lg with 16 | 32 -> () | _ -> failwith (string_of_int lg) in
  let rec aux l n = 
    if n = lg then
      l
    else
      let rec aux2 i = 
        if n + i = lg then
          i
        else if s.[n] = s.[n + i] then
          aux2 (succ i)
        else
          i in
      let i = aux2 1 in
      aux (((match s.[n] with 
        | '0' -> I_0
        | '1' -> I_1
        | 'n' -> I_n
        | 'm' -> I_m
        | 'i' -> I_i
        | 'd' -> I_d
        | _ -> assert false (* by definition of [Str.matched_group], we can prove that this case is never reached *)
      ), let () = 
           if not (match s.[n] with '0' | '1' -> true | _ -> false) then
             match i with
                 2 | 3 (* present in floating-point instruction (from 9.25 include to 9.46 include) *) | 4 | 8 | 12 -> ()
               | _ -> failwith (Printf.sprintf "%c %d" s.[n] i)
           else
             () in
         i) :: l) (n + i) in
  aux [] 0


let manual_of_in_channel o_file = 
  let module S = SH4_section in

  let t = match o_file with
    | Some s -> S.init s
    | None -> S.init_channel stdin in

  (** These regexp characterize the end of any C code present in the documentation *)
  let accol_end = Str.regexp " *} *" (* C code usually end with a '}' delimiter *) in
  let comment = Str.regexp " */\\*.*\\*/ *" (* a line containing C comment like /* */ *) in

  let matched_group_i n s = int_of_string (Str.matched_group n s) in
  let matched_group_t n s = let open T_bit in
    match Str.matched_group n s with
      | "\226\128\148" -> Tiret
      | "0" -> Zero
      | "1" -> One
      | "1/0" -> One_Zero
      | "Borrow" -> Borrow
      | "Carry" -> Carry
      | "LSB" -> LSB
      | "MSB" -> MSB
      | "Overflow" -> Overflow
      | "Result of" -> Result_of_
      | "Test" -> Test
      | "Underflow" -> Underflow 
      | "" -> Empty
      | _ -> failwith importation_error in


  let rec aux t l_section =
    match S.input_instr t with 
      | Last l_no_param -> 
        List.rev l_section
      | Next (l, t) -> 
        let l = List.flatten (List.rev l) in
        
        let decoder, l = (** [l1] contains the information between the beginning of the section and the line "Description" *)
          let l1, _, l = List.split_beg ((=) "Description") l in 
          
          match List.split_beg ((=) "") l1 with
            | [], _, _ | _ :: [], _, _ -> failwith importation_error
            | x1 :: x2 :: l1, _, l2 -> 
                (** Example : [x1] and [x2] contains
                    - "9.1 [whitespace] ADD [whitespace] ADD binary [whitespace] Arithmetic Instruction"
                    - " [whitespace] Binary Addition"
                *)

          let m l = Str.l_match (List.map (function x1, x2 -> Str.regexp x1, x2) l) in

          let contains_instruction x = m [ "\\(.+\\) +\\([A-Z][a-z]+\\)-?\\([A-Z][a-z]+\\)* Instruction", x ] in
          
          let (x1, x2), inst_ty = match () with
            | _ when contains_instruction x1 -> 
              let inst_ty = Str.matched_group 2 x1 ^ try "-" ^ Str.matched_group 3 x1 with _ -> "" in
              let x1, x2 = Str.matched_group 1 x1, x2 in
              (** In this part, we detect if the sequence "Delayed Branch Instruction" is present. *)
              (* (* to be completed *) let _ = 
                      match inst_ty with
                        | "Branch" -> 
                          (if m [ "\\(.+\\) +Delayed Branch Instruction", x2 ] then
                              Printf.printf "[[[[[\n%s\n]]]]]\n%!" (Str.matched_group 1 x2)
                           else 
                              ())
                        | _ -> () in*)
                (x1, x2), inst_ty
            | _ when contains_instruction x2 -> 
              (x1, Str.matched_group 1 x2), Str.matched_group 2 x2 ^ (try "-" ^ Str.matched_group 3 x2 with _ -> "")
            | _ -> failwith importation_error in 
          
          match (** suppress the block of eventually empty lines at the beginning and the end *)
            let f x = List.del_line (List.rev x) in f (f l2)
          with
            | [] | _ :: [] -> failwith importation_error
            | x_exe :: header :: l2 ->

          let dec_title = (** we rewrite correctly the title of the array *)
            match () with 
              | _ when m [ "^ *Execution *$", x_exe ] -> 
                (match Str.split (Str.regexp "  +") header with
                  | [ "Format" ; "Summary of Operation Instruction Code" ; "States" ; "T Bit" ] 
                  | [ "Format" ; "Summary of Operation" ; "Instruction Code" ; "States" ; "T Bit" ] 
                  | [ "Format" ; "Summary of Operation" ; "nstruction Code" ; "States" ; "T Bit" ] -> Menu
                  | [ "PR Format" ; "Summary of Operation Instruction Code" ; "States" ; "T Bit" ] 
                  | [ "PR" ; "Format" ; "Summary of Operation Instruction Code" ; "States" ; "T Bit" ] 
                  | [ "PR" ; "Format" ; "Summary of Operation" ; "Instruction Code" ; "States" ; "T Bit" ] -> Menu_PR
                  | [ "No. PR Format" ; "Summary of Operation Instruction Code" ; "States" ; "T Bit" ] -> Menu_NO_PR
                  | _ -> failwith importation_error)
              | _ when m [ "^ *Summary of +Execution *$", x_exe ] -> 
                      (** This case only applies to 9.37 and 9.38. Hopefully, the number of fields and the type of the data of each column are the same in both cases. *)
                (match String.sub x1 0 4 with "9.37" -> Menu_NO_SZ | "9.38" -> Menu_NO_PR | _ -> failwith importation_error)
              | _ -> failwith importation_error in

          let dec_tab = 
            List.map (fun (s, l2) -> 
              (if m [ "\\(.+\\) +\\([01nmid][01nmid][01nmid][01nmid][01nmid][01nmid][01nmid][01nmid][01nmid][01nmid][01nmid][01nmid][01nmid][01nmid][01nmid][01nmid]\\) +\\([0-9]+\\)\\(\226\128\147\\([0-9]+\\)\\)? *\\(.*\\)", s ] then
                  Dec_usual { before_code = Str.matched_group 1 s
                            ; inst_code = ( (* (fun l -> let () = analyse dec_title l in l) *) (list_of_string_01nmid (Str.matched_group 2 s)) )
                            ; states = (let open States in
                                            (match try Some (matched_group_i 5 s) with _ -> None with
                                              | None -> fun x -> Pos x
                                              | Some i_end -> fun i_beg -> Range (i_beg, i_end)) (matched_group_i 3 s))
                            ; t_bit = matched_group_t 6 s }
               else
                  let l_dash = Str.split (Str.regexp "  +") s in
                  let o, xs = 
                    match l_dash with
                      | ("0" | "1" as b) :: xs -> Some (b = "1"), xs
                      | xs -> None, xs in
                  if List.for_all ((=) "\226\128\148" (* dash symbol "-" *)) xs then
                    Dec_dash o
                  else
                    failwith importation_error), l2
                      
            ) (let l2 = structure_line l2 (* Remark : if [l2] is empty, it is an [importation_error] *) in
               match String.sub x1 0 4 with
                 | "9.31" -> (match l2 with x1 :: x2 :: _ -> [x1; x2] | _ -> failwith importation_error)
                 | "9.55" 
                 | "9.64" 
                 | "9.65" -> (match l2 with x :: _ -> [x] | _ -> failwith importation_error)
                 | _ -> l2) in

          { dec_other = (x1, x2, l1) 
          ; dec_title = dec_title 
          ; dec_title_long = header
          ; dec_tab = dec_tab 
          ; dec_inst_ty = inst_ty }, l in

        let l2, _, l = List.split_beg ((=) "Operation") l in (** [l2] contains the information between the line "Description" and the line "Operation" *)
        let l3, n, l = List.split_end (fun x -> List.exists (fun r -> Str.string_match r x 0) [ accol_end; comment ]) l in (** [l3 @ [n]] contains the C program between the line "Operation" and some human language information we are not interested *)
        let c_code = 
          (match decoder.dec_other with
            | (x1, _, _) when (match String.sub x1 0 4 with "9.50" | "9.92" -> true | _ -> false) -> 
              
              let r_bank = Str.regexp ".*_BANK" in
              let r_accol_end = Str.regexp ".*}" in
              let replace c_code =
                match List.split_beg (fun x -> Str.string_match r_bank x 0) c_code with
                  | l1, n0, _ :: ll ->
                    let l, n1, l2 = List.split_beg (fun x -> Str.string_match r_accol_end x 0) ll in
                    l1 @ List.flatten (
                      List.init (fun n -> List.map (Str.global_replace (Str.regexp "R._BANK") (Printf.sprintf "R%d_BANK" n)) ([n0] @ l @ [n1; ""])) 8), l2 
                  | _ -> failwith importation_error in
              fun c_code -> 
                let l1, l2 = replace c_code in
                let l2, l3 = replace l2 in
                l1 @ l2 @ l3
                  
            | _ -> fun x -> x) (l3 @ [n]) in

        aux t ({ position = S.pos t 
               ; explanation_desc = l2 
               ; c_code = c_code

               ; explanation_other = l 
               ; decoder = decoder } :: l_section) in

  (*preprocess_parse_c*) parse_c { entete = S.c_code t ; section = aux t [] }

type argument = 
  | File of string (* filename *)
  | Print_pc
  | Print_dec

module type ARG = 
sig
  val parse : unit -> argument list
end

module Arg : ARG = 
struct
  open Arg
  open Printf

  module Util =
  struct
    let error s = eprintf "error: %s\n" s; exit 1
  end

  open Util

  let usage_msg = "usage: " ^ Sys.argv.(0) ^ " option ...\n"

  let error s = error (sprintf "%s\n%s" s usage_msg)
  let l_dir = ref []
  let push e = 
    l_dir := e :: !l_dir

  let rec options () = 
    List.sort 
      (fun (x, _, _) (y, _, _) -> compare x y) 
      (Arg.align
         [ "-h", Unit print_help,
           " Display this list of options"
         ; "-f", String (fun s -> push (File s)),
           " File to input from"
         ; "-print_pseudocode", Unit (fun _ -> push Print_pc),
           " Display the C code" 
         ; "-print_decoder", Unit (fun _ -> push Print_dec),
           " Display the decoder information" ])

  and print_options oc =
    List.iter (fun (k, _, d) -> fprintf oc "%s: %s\n" k d) (options ())

  and print_help () = 
    begin
      print_endline usage_msg;
      print_options stdout;
      exit 0;
    end

  let parse () = 
    let () = Arg.parse (options ()) (fun _ -> error "invalid option") usage_msg in
    !l_dir
end


let _ = 
  let l = Arg.parse () in
  let manual = manual_of_in_channel (match try Some (List.find (function File _ -> true | _ -> false) l) with _ -> None with Some (File s) -> Some s | _ -> None) in

  if List.exists ((=) Print_pc) l then
    begin
      List.iter (fun s -> Printf.printf "%s\n" s) manual.entete.init;
      
      List.iter (fun sec -> 
        begin
          Printf.printf "/* 9.%d */\n" sec.position;
          Printf.printf "%s\n%!" (List.fold_left (Printf.sprintf "%s%s\n") "" sec.c_code.init);
(*          Check.decoder_title sec;*)
        end;
      ) manual.section;
      
      Printf.printf "%!";
    end

  else if List.exists ((=) Print_dec) l then
    begin
      List.iter (fun sec -> 
        List.iter (function
          | Dec_usual line, _ ->
            begin
              Printf.printf "#%s#\n" ((*List.fold_left (Printf.sprintf "%s%s|") "" *) sec.decoder.dec_title_long);
              Printf.printf "|%s|\n" line.before_code ;
              (*List.iter (fun s -> Printf.printf "|%s|\n" s) l2;
                Printf.printf "\n";*)
            end
          | Dec_dash _, _ -> ()) sec.decoder.dec_tab
      ) manual.section;
      
      Printf.printf "%!";
    end

  else
    output_value stdout manual

end
