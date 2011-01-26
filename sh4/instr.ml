(**
SimSoC-Cert, a Coq library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the SH4 architecture following the:

SH-4, Software Manual, Renesas 32-Bit RISC, Rev.6.00 2006.09

Page numbers refer to Renesas_SH4_2006.pdf.


*)

open Util
open Pdf_page
open Sh4_section
open C_parse
open Manual

let display_dec = false
let display_c = true

let mk_code l = 
  { init = l
  ; code = C_parse.c_of_program (List.fold_left (Printf.sprintf "%s%s\n") "" l) }

let preprocess_parse_c : string list manual -> raw_c_code manual = fun m -> 
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

module String_map = Map.Make (struct type t = string let compare = compare end)
module Int_set = Set.Make (struct type t = int let compare = compare end)

let _ = 
  let module S = SH4_section in

  let t = 
    match try Some Sys.argv.(1) with _ -> None with
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

  let map_analyse = ref String_map.empty in
  let analyse dec_title l = 
    match dec_title with
      | Menu -> 
	map_analyse :=
	List.fold_left (
	  fun map -> 
	    let f s nb = 
	      String_map.add s (if String_map.mem s map then Int_set.add nb (String_map.find s map) else Int_set.empty) map
	    in
	    function
	  | I_1, nb -> f "1" nb
	  | I_0, nb -> f "0" nb
	  | I_n, nb -> f "n" nb
	  | I_m, nb -> f "m" nb
	  | I_i, nb -> f "i" nb
	  | I_d, nb -> f "d" nb) !map_analyse l
      | Menu_PR 
      | Menu_NO_PR  
      | Menu_NO_SZ -> () in

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
                let l1, n0, _ :: ll = List.split_beg (fun x -> Str.string_match r_bank x 0) c_code in
                let l, n1, l2 = List.split_beg (fun x -> Str.string_match r_accol_end x 0) ll in
                l1 @ List.flatten (
                  List.init (fun n -> List.map (Str.global_replace (Str.regexp "R._BANK") (Printf.sprintf "R%d_BANK" n)) ([n0] @ l @ [n1; ""])) 8), l2 in
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


  let manual = (*preprocess_parse_c*) parse_c { entete = S.c_code t ; section = aux t [] }  in

  let () = output_value stdout manual in
  let () = exit 0 in

  begin
    (if false then (* this part is used to know the size of each register inside the decoder array *)
      begin
	String_map.fold (fun k m () -> Printf.eprintf "%s [%s]\n%!" k (Int_set.fold (fun k acc -> Printf.sprintf "%s%d " acc k) m "")) !map_analyse ();
      end
    (* 
       0 [1 2 3 4 5 6 7 8 9 10 11 12 ]
       1 [1 2 3 4 5 7 ]
       d [4 8 12 ]
       i [8 ]
       m [4 ]
       n [4 ]
    *) 
    else
      ());
    if false && display_c then
      begin 
	List.iter (fun s -> Printf.printf "%s\n" s) manual.entete.init;
      end; 
    List.iter (fun sec -> 
      begin 
        if false && display_c then
          begin
            Printf.printf "/* 9.%d */\n" sec.position;
            Printf.printf "%s\n%!" (List.fold_left (Printf.sprintf "%s%s\n") "" sec.c_code.init);
          end;
        if display_c then
          begin
          match sec.decoder.dec_title with
            | Menu ->
            (*Printf.printf "/* 9.%d */" sec.position;*)

            (** algorithm for coupling the line present in the decoder and the pseudo code *)
            let n1 = List.fold_left (fun acc -> function Dec_usual _, _ -> succ acc | _ -> acc) 0 sec.decoder.dec_tab (** number of line in the array *)
            and n2 = List.length sec.c_code.code (** number of function defined in C *) in
            let () = if n1 = n2 then () else assert false in

              (** test to verify that every function has a name in uppercase ('_' and number are allowed) *)
            List.iter (let module C = Cabs in
                       function 
                         | C.FUNDEF ((_, (s, _, _, _)), _, _, _) -> let m r = Str.string_match (Str.regexp r) s 0 in
                           match () with 
                             | _ when m "[0-9_A-Z]+$" -> ()
                             | _ -> assert false (*Printf.printf "%s\n%!" s*) ) sec.c_code.code
            | Menu_PR -> 
              begin
              Printf.printf "/* 9.%d PR */" sec.position;

              (** test to verify that every function has a name in uppercase ('_' and number are allowed) *)
              let n1 = List.fold_left (fun acc -> function Dec_usual _, _ -> succ acc | _ -> acc) 0 sec.decoder.dec_tab (** number of line in the array *)
              and n2 = 
              List.fold_right (let module C = Cabs in
                         function 
                           | C.FUNDEF ((_, (s, _, _, _)), _, _, _) -> let m r = Str.string_match (Str.regexp r) s 0 in
                             match () with 
                               | _ when m "[0-9_A-Z]+$" -> succ
                               | _ when m "[0-9_a-z]+$" -> (fun x -> x)
                               | _ -> assert false ) sec.c_code.code 0 in
              let () = if n1 = n2 then () else Printf.printf "/* %d %d */\n" n1 n2 in
              ()
              end
            | Menu_NO_PR -> 
              begin
              Printf.printf "/* 9.%d NOPR */" sec.position;

              (** test to verify that every function has a name in uppercase ('_' and number are allowed) *)
              List.iter (let module C = Cabs in
                         function 
                           | C.FUNDEF ((_, (s, _, _, _)), _, _, _) -> let m r = Str.string_match (Str.regexp r) s 0 in
                             match () with 
                               | _ when m "[0-9_A-Z]+$" -> ()
                               | _ when m "[0-9_a-z]+$" -> Printf.printf "%s\n%!" s 
                               | _ -> assert false ) sec.c_code.code;
              end
            | Menu_NO_SZ -> 
              begin
              Printf.printf "/* 9.%d NOSZ */" sec.position;

              (** test to verify that every function has a name in uppercase ('_' and number are allowed) *)
              List.iter (let module C = Cabs in
                         function 
                           | C.FUNDEF ((_, (s, _, _, _)), _, _, _) -> let m r = Str.string_match (Str.regexp r) s 0 in
                             match () with 
                               | _ when m "[0-9_A-Z]+$" -> ()
                               | _ when m "[0-9_a-z]+$" -> Printf.printf "%s\n%!" s 
                               | _ -> assert false ) sec.c_code.code;
              end

          end;

        if display_dec then
          List.iter (function
            | Dec_usual line, _ ->
              begin
                Printf.printf "#%s#\n" ((*List.fold_left (Printf.sprintf "%s%s|") "" *) sec.decoder.dec_title_long);
                Printf.printf "|%s|\n" line.before_code ;
                    (*List.iter (fun s -> Printf.printf "|%s|\n" s) l2;
                Printf.printf "\n";*)
              end
            | Dec_dash _, _ -> ()) sec.decoder.dec_tab;

      end) manual.section;

    Printf.printf "%!";
  end
