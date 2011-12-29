(**
SimSoC-Cert, a Coq library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the SH4 architecture following the:

SH-4, Software Manual, Renesas 32-Bit RISC, Rev.6.00 2006.09

Page numbers refer to Renesas_SH4_2006.pdf.


*)

open Pervasive
open Cparser
open Manual

module C_parse : C_PARSE with type t = Cabs.definition list = 
struct
  type t = Cabs.definition list

  let c_of_file fic : Cabs.definition list option = 
    let ic = open_in_bin fic in
    let v = try Some (Parser.file Lexer.initial (Lexer.init "#" ic)) with _ -> None in
    let _ = close_in ic in
    v

  let c_of_program_ c_of_file suf str = 
    let fic = Filename.temp_file "test" suf in
    let oc = open_out fic in
    let () = Printf.fprintf oc "%s\n" str in
    let () = close_out oc in
    let v = c_of_file fic in
    let () = Unix.unlink fic in
    v

  let c_of_program = c_of_program_ c_of_file ""

  let list_of_ic ic = 
    let rec aux l = 
      match try Some (input_line ic) with _ -> None with
        | None -> List.rev l
        | Some s -> aux (s :: l) in
    aux []

  let process f s = 
    let ic, oc = Unix.open_process f in
    let () = output_string oc s in
    let () = close_out oc in
    let l = list_of_ic ic in
    let _ = Unix.close_process (ic, oc) in
    l

  let preprocess = 
    c_of_program_ (fun fic -> 
      let ic = Unix.open_process_in (Printf.sprintf "gcc -E -U__GNUC__ %s" fic) in
      let l = list_of_ic ic in
      let _ = Unix.close_process_in ic in
      l
    ) ".c"

  let expand_line_space l =
    snd
      (List.fold_left (fun (pos1, acc) s ->
        match Str.str_match "# \\([0-9]+\\) " s [1] with
          | Some [n] -> 
            let pos2 = int_of_string n in
            let rec aux pos1 acc = 
              if pos1 = pos2 then 
                pos1, acc
              else
                aux (succ pos1) ("" :: acc) in
            aux pos1 acc
          | _ -> 
            succ pos1, s :: acc) (1, []) l)

  type raw_c_code = 
    { init : string list (* WARNING [init] is unused *)
    ; code : t option (** representation of the C pseudocode, natural order : first element in the list = first line *) }

  let mk_code l = 
    { init = l
    ; code = c_of_program (List.fold_left (Printf.sprintf "%s%s\n") "" l) }

  let organize_header = function true -> failwith "this is unimplemented" | _ -> mk_code

  let organize_body = organize_header

  let print oc l = List.iter (Printf.fprintf oc "%s\n") l.init

  let get_code t = t.code

  let parse_whole l (pos, l_pos) m = 
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
	l in

    fun arrange_order -> 
      { entete = organize_header arrange_order l
      ; section = List.map2 (fun l i -> { i with c_code = organize_body arrange_order l }) ll m.section }

end
