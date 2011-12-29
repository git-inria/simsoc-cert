(**
SimSoC-Cert, a Coq library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the SH4 architecture following the:

SH-4, Software Manual, Renesas 32-Bit RISC, Rev.6.00 2006.09

Page numbers refer to Renesas_SH4_2006.pdf.


*)

open Shparsing.Pervasive
open Shparsing.Manual

module C_parse : C_PARSE = 
struct
  type t = Cil.global list

  let c_of_file fic : t option = 
    try Some (Frontc.parse fic ()).Cil.globals with _ -> None

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

  type raw_c_code = t

  let mk_code _ _ = failwith "The CIL library must consider the entire program because some variable checking processes are performed"

  let organize_header = mk_code 
  let organize_body = mk_code

  let mk_code f arrange_order l = 
    if arrange_order then
      BatList.flatten (f (fun f -> BatList.partition f l))
    else
      l

  open BatMap

  let organize_header2 =
    let open Cil in
    mk_code (fun partition -> 
      let l_fundef, l_other = partition (function GFun _ -> true | _ -> false) in
      let map_s, _ = List.fold_left (fun (map_s, pos) s -> StringMap.add s pos map_s, succ pos) (StringMap.empty, 0) Patching.Data.Semantic_compcert.fundef_order in
      [ l_other 
      ; BatList.map snd (IntMap.bindings (List.fold_left (fun map_i -> function Cil.GFun ({svar = {vname = n}}, _) as x -> IntMap.add (StringMap.find n map_s) x map_i) IntMap.empty l_fundef)) ])

  let organize_body2 = 
    let open Cil in
    mk_code (fun partition -> 
      let l_maj, l_min = partition (function GFun ({svar = {vname = n}}, _) | GVarDecl ({vname = n}, _) -> Str.l_match [ Str.regexp "[A-Z_0-9]+", n ]) in
      [ List.rev l_min ; l_maj ])

  let print oc = 
    List.iter (Cil.dumpGlobal Cil.defaultCilPrinter oc)

  let get_code x = Some x

  let parse_whole l (pos, l_pos) m = 
    let open Cil in

    let rec aux l_pos l acc1 acc2 =
      match l with 
	| x :: xs -> 
	  if match x with GFun (_, l) -> l.line > List.hd l_pos | _ -> true then
	    aux l_pos xs (x :: acc1) acc2
	  else
	    aux (List.tl l_pos) xs [x] (acc1 :: acc2)
	| [] -> acc1 :: acc2 in

    let Some x = c_of_program (List.fold_left (Printf.sprintf "%s%s\n") "" (List.rev l)) in

    let x :: xs = aux l_pos (List.rev x) [] [] in

    fun arrange_order ->
      { entete = organize_header2 arrange_order x ; section = BatList.map2 (fun e i -> {i with c_code = organize_body2 arrange_order e}) xs m.section }

end
