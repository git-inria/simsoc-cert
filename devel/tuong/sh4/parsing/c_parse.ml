(**
SimSoC-Cert, a Coq library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the SH4 architecture following the:

SH-4, Software Manual, Renesas 32-Bit RISC, Rev.6.00 2006.09

Page numbers refer to Renesas_SH4_2006.pdf.


*)

open Shparsing.Pervasive
open Shparsing.Manual
open Frontc

module C_parse : C_PARSE = 
struct
  type t = Cabs.definition list

  let option_of_parsing_result f = 
    match try f stderr with _ -> PARSING_ERROR with
    | PARSING_ERROR -> None
    | PARSING_OK l -> Some l

  let c_of_file fic : Cabs.definition list option = 
    option_of_parsing_result (parse_file fic)

  let c_of_program str = 
    let ic, oc = Unix.pipe () in
    let oc = Unix.out_channel_of_descr oc in
    let () = output_string oc str in
    let () = close_out oc in
    option_of_parsing_result (parse_channel (Unix.in_channel_of_descr ic))

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
    let c_of_program_ c_of_file suf str = 
      let fic = Filename.temp_file "test" suf in
      let oc = open_out fic in
      let () = Printf.fprintf oc "%s\n" str in
      let () = close_out oc in
      let v = c_of_file fic in
      let () = Unix.unlink fic in
      v in
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

  type raw_c_code = t option

  let mk_code f arrange_order l = 
    let v = c_of_program (List.fold_left (Printf.sprintf "%s%s\n") "" l) in
    if arrange_order then
      Some (BatList.flatten (f (fun f -> BatList.partition f (let Some l = v in l))))
    else
      v

  open BatMap

  let organize_header =
    mk_code (fun partition -> 
      let l_fundef, l_other = partition (function Cabs.FUNDEF _ -> true | _ -> false) in
      let map_s, _ = List.fold_left (fun (map_s, pos) s -> StringMap.add s pos map_s, succ pos) (StringMap.empty, 0) Data.Semantic_compcert.fundef_order in
      [ l_other 
      ; BatList.map snd (IntMap.bindings (List.fold_left (fun map_i -> function Cabs.FUNDEF ((_, _, (n, _, _, _)), _) as x -> IntMap.add (StringMap.find n map_s) x map_i) IntMap.empty l_fundef)) ])

  let organize_body = 
    mk_code (fun partition -> 
      let l_maj, l_min = partition (function Cabs.FUNDEF ((_, _, (n, _, _, _)), _) -> Str.l_match [ Str.regexp "[A-Z_0-9]+", n ]) in
      [ List.rev l_min ; l_maj ])

  let print oc = function
    | None -> assert false
    | Some x -> 
      let _ = Cprint.out := oc in
      Cprint.print_defs x

  let get_code t = t
end
