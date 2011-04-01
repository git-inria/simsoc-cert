(**
SimSoC-Cert, a toolkit for generating certified processor simulators
See the COPYRIGHTS and LICENSE files.

Driver for ocamlbuild.
*)

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

(** [ln_s] behaves as the previously defined [ln_s] except that a 'touch' to the destination file is done in the case it already exists. *)
let ln_s src dest = 
  if Sys.file_exists dest then
    Cmd (S [ A "touch" ; A "-h" ; P dest ])
  else
    ln_s src dest

(** [rule_finalize _ f o_file] provides a value of type [action] which can be use with [rule]. 
  It creates a link to the binary if it does not exist yet. 
  If [o_file] = [Some filename], the name of the link is [filename], otherwise it is same as the binary.
  The modification time of the link is always older than the binary. 
  [f] is an extra action which can be performed after the creation of the link. *)
let rule_finalize nc f_cmd o_file env _ =
  let fic = env ("%." ^ nc) in
  let open Pathname in
    Seq (ln_s (Printf.sprintf "%s_build" 
                 ((* FIXME use [ Str.split (Str.regexp_string "/") fic ] *)
                   (** return the number of occurence of '/' in [fic] *)
                   let rec aux pos l = 
                     match try Some (String.rindex_from fic pos '/') with _ -> None with
                       | None -> l
                       | Some pos -> aux (pred pos) (Printf.sprintf "%s../" l) in
                   aux (pred (String.length fic)) "")
               / fic) (concat parent_dir_name (match o_file with None -> remove_extensions fic | Some file -> file))
          (* FIXME find a more generical way to create this symbolic link *) :: f_cmd fic)

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

let l_compcert = List.map ((/) "compcert")
  [ "lib" ; "common" ; arch / variant ; arch ; "backend" ; "cfrontend" ; "driver" 
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
      List.iter (fun x -> Pathname.define_context x ("compcert" :: (* The directory [compcert/cfrontend] needs to have a relative path notion to [cparser], but [cparser] is inside [compcert], so we have to add [compcert]. *)
                                                        l_compcert)) l_compcert;
      
      (**   - the SimSoC-Cert project : *)
      List.iter (fun (n, l) -> define_context n l)
        [ "arm6", l_compcert @ [ "arm6/extraction" ]
        ; "arm6/parsing", [ "simgen" ]
        ; "arm6/extraction", [ "compcert/extraction" ; "simgen/extraction" ] 
        ; "arm6/test", l_compcert @ [ "arm6" ; "compcert/extraction" ; "simgen/extraction" ; "arm6/extraction" ]
        ; "simgen", l_compcert @ [ "simgen/extraction" ; "sh4/parsing" ]
        ; "simgen/extraction", [ "compcert/extraction" ]
        ; "sh4/parsing", [ "compcert/cfrontend" (* we just use the library [Cparser] which is virtually inside [cfrontend] *) ]
        ; "sh4/extraction", [ "compcert/extraction" ; "simgen/extraction" ] 
        ; "sh4/test", [ "sh4/extraction" ] ];

      (** ----------------------------------- *)
      (** activation of specific options for : *)
      (**   - the compcert project : *)  (* FIXME determine how to include compcert/myocamlbuild.ml *)
      (* force linking of libCparser.a when use_Cparser is set *)
      flag ["link"; "ocaml"; "native"; "use_Cparser"]
        (S[A"compcert/cfrontend/libCparser.a"]);
      flag ["link"; "ocaml"; "byte"; "use_Cparser"]
        (S[A"-custom"; A"compcert/cfrontend/libCparser.a"]);
      
      (* make sure libCparser.a is up to date *)
      dep  ["link"; "ocaml"; "use_Cparser"] ["compcert/cfrontend/libCparser.a"];

      (**   - the SimSoC-Cert project : *)
      flag ["ocaml"; "compile" ; "pseudocode_native"] (S [ A "-unsafe" 
                                                         ; A "-noassert" 
                                                         ; A "-inline" ; A "10000" ]);

      (** ----------------------------------- *)
      (** declaration of extra rules *)
      rule "[simgen/%_finalize] perform a ln -s to the binary and strip it" 
        ~prod: "simgen/%_finalize" ~deps: [ "simgen/%.native" ]
        (fun env -> rule_finalize "native" (fun fic -> [ Cmd (S [ A "strip" ; P fic ]) ]) (None (*Some "simgen/simgen"*)) (fun s -> "simgen" / (env s)));

      rule "[%_finalize] perform a ln -s to the binary" 
        ~prod: "%_finalize" ~deps: [ "%.native" ] (* FIXME rename finalize into finalize_nc *)
        (rule_finalize "native" (fun _ -> []) None);

      rule "[%_finalize_bc] perform a ln -s to the binary" 
        ~prod: "%_finalize_bc" ~deps: [ "%.byte" ]
        (rule_finalize "byte" (fun _ -> []) None);
    end
  | _ -> ()
