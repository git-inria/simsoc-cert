(**
SimSoC-Cert, a Coq library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the SH4 architecture following the:

SH-4, Software Manual, Renesas 32-Bit RISC, Rev.6.00 2006.09

Page numbers refer to Renesas_SH4_2006.pdf.


*)

open Patch
module IntMap = BatMap.Make (BatInt)

let main enum_in = 
  let l_map = 
    let f_add l_patch (act, pos) = 
      let p, nb = 
        match act, pos with
          | Replace_tilde nb, P p -> p, nb
          | _, R (p, nb) -> p, nb
          | _, P p -> p, 1 in
      let f_fold f acc = BatEnum.fold (fun acc nb -> f (p + nb) acc) acc (BatEnum.(--) 1 nb) in
      let rec aux = function
        | map :: maps ->
          if f_fold (fun p b -> b || IntMap.mem p map) false then
            map :: aux maps
          else
            f_fold (fun p -> IntMap.add p (act, pos)) map :: maps
        | [] -> [ f_fold (fun p -> IntMap.add p (act, pos)) IntMap.empty ] in
      aux l_patch in
    
    let l_patch, l_end = 
      List.fold_left (fun acc (act, l_pos) -> 
        List.fold_left (fun (l_patch, l_end) pos ->
          match act with (* determining if the action will add or remove lines. In theses cases, we delay these actions. *)
            | Replace_first (All, _) | Add_line_aft _ -> l_patch, (act, pos) :: l_end
            | _ -> f_add l_patch (act, pos), l_end
        ) acc l_pos) ([], []) Data.patch in
    BatList.flatten [ l_patch ; List.fold_left f_add [] (List.rev l_end) ] in

  let patch enum flat_map = 
    BatEnum.flatten
      (BatEnum.map (fun e -> 
        let Some (o, s0) = BatEnum.get e in 
        match o with
          | None -> let e = BatEnum.map snd e in let () = BatEnum.push e s0 in e
          | Some (v, _) ->
            let l = s0 :: BatList.map snd (BatList.of_enum e) in
            BatList.enum
              (match v with
                | Replace_all (reg, s_new) -> BatList.map (Str.global_replace (Str.regexp_string reg) s_new) l
                | Replace_first (reg, s_new) -> 
                  let r reg = BatList.map (Str.replace_first reg s_new) l in
                  (match reg with
                    | All -> [s_new]
                    | S reg -> r (Str.regexp_string reg)
                    | Re reg -> r (Str.regexp reg))
                | Replace_tilde n -> 
                  (match n, l with
                    | 1, [s] -> [ let s_new = Str.replace_first (Str.regexp_string "~") "!" s in if s_new = s then Str.replace_first (Str.regexp_string "\226\136\188") "!" s else s_new ]
                    | 2, [s1; s2] -> [ Str.replace_first (Str.regexp_string "~") "" s1 ; BatString.splice s2 (BatString.rfind_from s2 (BatString.find s1 "~") " ") 1 "!" ]
                    | _ -> assert false)
                | Add_line_aft s -> BatList.flatten [ l ; [ s ] ]
                | Add_char_beg s_beg -> BatList.map ((^) s_beg) l
                | Add_char_end s_end -> BatList.map (fun x -> x ^ s_end) l
                | Comment -> BatList.map (fun s -> "/*" ^ s ^ "*/") l)
       )
         (BatEnum.group fst
            (BatEnum.mapi (fun i s -> IntMap.Exceptionless.find (i + 2) flat_map, s) enum))
      ) in

  List.fold_left patch enum_in l_map

let _ = 
  let l1, l2 =
    let rec aux o1 o2 l = match o1, o2, l with
      | _, None, "-o" :: fic_out :: l -> aux o1 (Some fic_out) l
      | None, _, s :: l when (try s.[0] <> '-' with _ -> false) -> aux (Some s) o2 l
      | Some _, Some _, _ | _, _, [] -> o1, o2
      | _, _, _ :: l -> aux o1 o2 l in
    aux None None (List.tl (Array.to_list Sys.argv)) in

  (match l2 with
  | Some fic_out -> BatFile.write_lines fic_out
  | None -> BatEnum.iter (BatIO.write_line BatIO.stdout))
    (main
       (match l1 with
       | Some fic_in -> BatFile.lines_of fic_in
       | None -> BatIO.lines_of BatIO.stdin))
