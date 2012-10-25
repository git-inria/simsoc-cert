(**
SimSoC-Cert, a toolkit for generating certified processor simulators
See the COPYRIGHTS and LICENSE files.

Driver for ocamlbuild.
This file is the main program of ocamlbuild. After the invocation of 'ocamlbuild', this file is executed. It contains the dependencies of the directory, as these dependencies are not calculated by ocamlbuild by default.
Note that every '_tags' files can be deleted and put in this file, by using directly a call to the API of ocamlbuild.
Finally, we can modify the behaviour of ocamlbuild, by writing an OCaml Turing-complete program here, as it is done for performing a symbolic link for example.
*)

(** The library of Cparser is now located in /compcert/cparser in CompCert-1.11 *)

module Ocamlbuild_plugin = 
struct
  (** This module replaces the module [Ocamlbuild_plugin] by adding the possibility to use the tags [warn_%s] and [warn_error_%s] where '%s' is the english word of a number, e.g. "twenty_nine" for 29. *)
  include Ocamlbuild_plugin

  let ocaml_warn_flag (c, i) =
    let open Printf in
    begin
      flag ["ocaml"; "compile"; sprintf "warn_%s" (String.uppercase c)]
        (S[A"-w"; A (sprintf "+%d" i)]);
      flag ["ocaml"; "compile"; sprintf "warn_error_%s" (String.uppercase c)]
        (S[A"-warn-error"; A (sprintf "+%d" i)]);
      flag ["ocaml"; "compile"; sprintf "warn_%s" (String.lowercase c)]
        (S[A"-w"; A (sprintf "-%d" i)]);
      flag ["ocaml"; "compile"; sprintf "warn_error_%s" (String.lowercase c)]
        (S[A"-warn-error"; A (sprintf "-%d" i)])
    end

  let dispatch f = 
    dispatch & function 
      | After_rules -> 
        begin
          List.iter ocaml_warn_flag [ "twenty_nine", 29 ];
          f After_rules;
        end
      | x -> f x
end

open Ocamlbuild_plugin


module Symbolic_link = 
struct
  (** The task of this module is to save the modification time of the binary we are constructing (in _build) and do a link to it before exiting the program. *)

  type time = 
      { access : float
      ; modification : float
      ; status_change : float }

  let time_of_file fic = 
    if Sys.file_exists fic then
      let open Unix.LargeFile in
      let tm = lstat fic in
      Some { access = tm.st_atime
           ; modification = tm.st_mtime
           ; status_change = tm.st_ctime }
    else
      None

  let mod_time = ref None

  let file_name = Sys.argv.(pred (Array.length Sys.argv))

  (** We store at the beginning of the execution of ocamlbuild the date of modification of the file [_build/%s.native] where '%s' is the name of the rule given.
      Note that by default, we take the 'native' version. *)
  let begin_fun () = 
    mod_time := time_of_file ("_build" / file_name)

  (** At the end of the execution, it will perform a link to the binary in question. *)
  let end_fun () = 
    match time_of_file ("_build" / file_name) with
      | Some t2 ->
        let dest = Pathname.remove_extensions file_name in
        let ln_s dest = 
          let fic = file_name in
          ln_s 
            (Printf.sprintf "%s_build" 
               ((* FIXME use [ Str.split (Str.regexp_string "/") fic ] *)
                (** return the number of occurence of '/' in [fic] *)
                let rec aux pos l = 
                  match try Some (String.rindex_from fic pos '/') with _ -> None with
                    | None -> l
                    | Some pos -> aux (pred pos) (Printf.sprintf "%s../" l) in
                aux (pred (String.length fic)) "")
             / fic) dest in
        
        Command.execute 
          (match time_of_file dest with
            | Some t_ln ->
              if (match !mod_time with Some t1 -> t1.modification = t2.modification | None -> true) && t2.modification <= t_ln.modification then
                Nop
              else
                Seq [ rm_f dest ; ln_s dest ]
            | _ -> ln_s dest)
      | None -> ()

end



(** --------------------------------------------- *)
(** The first declaration in 'compcert/Makefile' assign all the folders used by the compcert project to the variable 'DIRS'. 
  We do the same here to the variable [l_compcert]. *)

let arch, variant = (** we read the file compcert/Makefile.config to get the value associated to ARCH and VARIANT. *)
  let ic = open_in ("compcert" / "Makefile" -.- "config") in
  let rec aux l = 
    match try Some (input_line ic) with _ -> None with
      | None -> l
      | Some s -> 
        aux (match try Some (let i = String.index s '=' in 
                             String.sub s 0 i, 
                             let i = succ i in String.sub s i (String.length s - i)) with _ -> None with
          | None -> l
          | Some (a, b) -> (a, b) :: l) in
  let l = aux [] in
  let _ = close_in ic in
  let find s = List.assoc s l in
  find "ARCH", find "VARIANT"

(** CompCert-1.9 -> 1.11, add cparser directory to the list *)
let l_compcert = List.map ((/) "compcert")
  [ "lib"; "common"; arch / variant; arch; "backend"; "cparser"; "cfrontend"; "driver"
  ; "extraction" ]

(** --------------------------------------------- *)

(** In general, a directory has only itself as its scope (we have by default the equation : Pathname.define_context dir [dir]). 
  This function provides the possibility to add manually all the directory where there is some dependencies to the considered directory.
  Note that we can add more directory than required as long as there is no conflict between the name of files. However, the complexity time of ocamlbuild may vary. *)
let define_context dir l = 
  Pathname.define_context dir (l @ [dir])

let _ = dispatch & function
  | After_rules -> 
    begin
      (** ----------------------------------- *)
      (** definition of context for : *)
      (**   - the compcert project : *)
      List.iter (fun x -> Pathname.define_context x ("compcert" :: (* The directory [compcert/cparser] needs to have a relative path notion to [cparser], but [cparser] is inside [compcert], so we have to add [compcert]. *)
                                                        l_compcert)) l_compcert;
      
      (**   - the SimSoC-Cert project : *)
      List.iter (fun (n, l) -> define_context n l)
        [ "coq/extraction", l_compcert
        ; "simgen", l_compcert @ [ "simgen/extraction" ]
        ; "simgen/extraction", [ "compcert/extraction" ; "coq/extraction" ]

        ; "arm6/parsing", [ "simgen" ]
        ; "arm6/coq/extraction", [ "compcert/extraction" ; "coq/extraction" ; "simgen/extraction" ] 
        ; "arm6/simlight/extraction", l_compcert @ [ "coq/extraction" ]
        ; "arm6/simlight2/extraction", l_compcert @ [ "coq/extraction" ]
        ; "arm6/test", l_compcert @ [ "arm6/coq" ; "compcert/extraction" ; "coq/extraction" ; "simgen/extraction" ; "arm6/coq/extraction" ; "arm6/test/extraction" ]
        ; "arm6/test/extraction", l_compcert @ [ "coq/extraction" ; "arm6/coq/extraction" ]

        ; "sh4/parsing", [ "compcert/cparser" (* we just use the library [Cparser] which is virtually inside [cparser] now in CompCert-1.11 *) ]
        ; "sh4/coq/extraction", [ "compcert/extraction" ; "coq/extraction" ; "simgen/extraction" ] 
        ; "sh4/simlight/extraction", l_compcert @ [ "coq/extraction" ]
        ; "sh4/test", l_compcert @ [ "sh4/coq" ; "compcert/extraction" ; "coq/extraction" ; "simgen/extraction" ; "sh4/coq/extraction" ; "sh4/test/extraction" ]
        ; "sh4/test/extraction", l_compcert @ [ "coq/extraction" ; "sh4/coq/extraction" ]

        ; "devel/tuong/sh4/parsing_frontc", [ "devel/tuong/sh4/patching" ] ];

      (** ----------------------------------- *)
      (** activation of specific options for : *)
      (**   - the compcert project : *)  (* FIXME determine how to include compcert/myocamlbuild.ml *)
      (* force linking of libCparser.a when use_Cparser is set *)
      flag ["link"; "ocaml"; "native"; "use_Cparser"]
        (S[A"compcert/cparser/libCparser.a"]);
      flag ["link"; "ocaml"; "byte"; "use_Cparser"]
        (S[A"-custom"; A"compcert/cparser/libCparser.a"]);
      
      (* make sure libCparser.a is up to date *)
      dep  ["link"; "ocaml"; "use_Cparser"] ["compcert/cparser/libCparser.a"];

      (**   - the SimSoC-Cert project : *)
      flag ["ocaml"; "compile" ; "pseudocode_native"] (S [ A "-unsafe" 
                                                         ; A "-noassert" 
                                                         ; A "-inline" ; A "10000" ]);

      (** ----------------------------------- *)
      Symbolic_link.begin_fun ();
    end
  | _ -> ()

let _ = at_exit Symbolic_link.end_fun
