open Manual
(* open Cparser *)

module Decoder = 
struct
  let map_analyse = ref String_map.empty
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
      | Menu_NO_SZ -> ()
  let print () = (* this part is used to know the size of each register inside the decoder array *)
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
end

let decoder_title sec =
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
