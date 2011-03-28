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

(** [ln_s] behaves as the previously defined [ln_s] except that nothing is done in the case the destination file already exists. *)
let ln_s src dest = 
  if Sys.file_exists dest then
    Nop
  else
    ln_s src dest

(** [rule_finalize _ f] provide a function which can be use with [rule]. It creates a link to the binary. [f] is an extra action which can be performed after the creation of the link. *)
let rule_finalize nc f_cmd env _ =
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
               / fic) (concat parent_dir_name (remove_extensions fic))
          (* FIXME find a more generical way to create this symbolic link *) :: f_cmd fic)

(** --------------------------------------------- *)
(** compcert specific informations *)

let arch, variant = 
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

let _ = dispatch & function
  | After_rules ->
    let define_context dir l = Pathname.define_context dir (l @ [dir]) in
    begin
      (** ----------------------------------- *)
      (** definition of context *)
      List.iter (fun x -> Pathname.define_context x ("compcert" :: (* The directory [compcert/cfrontend] needs to have a relative path notion to [cparser], but [cparser] is inside [compcert], so we have to add [compcert]. *)
                                                        l_compcert)) l_compcert;
      define_context "arm6" (l_compcert @ [ "extract/tmp" ]);
      define_context "extract/tmp" [ "arm6" ; "compcert/extraction" ; "pseudocode/extraction" ];
      define_context "pseudocode" (l_compcert @ [ "pseudocode/extraction" ; "sh4" ]);
      define_context "pseudocode/extraction" [ "compcert/extraction" ];
      define_context "arm6/parsing" [ "pseudocode" ];
      define_context "sh4" [ "compcert/cfrontend" (* we just use the library [Cparser] which is virtually inside [cfrontend] *) ];
      define_context "test" (l_compcert @ [ "extract/tmp" ]);

      (** ----------------------------------- *)
      (** activation of specific options for... *)
      (**   ... compcert files *)
      (* force linking of libCparser.a when use_Cparser is set *)
      flag ["link"; "ocaml"; "native"; "use_Cparser"]
        (S[A"compcert/cfrontend/libCparser.a"]);
      flag ["link"; "ocaml"; "byte"; "use_Cparser"]
        (S[A"-custom"; A"compcert/cfrontend/libCparser.a"]);
      
      (* make sure libCparser.a is up to date *)
      dep  ["link"; "ocaml"; "use_Cparser"] ["compcert/cfrontend/libCparser.a"];

      (**   ... other files *)
      flag ["ocaml"; "compile" ; "pseudocode_native"] (S [ A "-unsafe" 
                                                         ; A "-noassert" 
                                                         ; A "-inline" ; A "10000" ]);

      (** ----------------------------------- *)
      (** declaration of extra rules *)
      rule "[pseudocode/%_finalize] perform a ln -s to the binary and strip it" 
        ~prod: "pseudocode/%_finalize" ~deps: [ "pseudocode/%.native" ]
        (fun env -> rule_finalize "native" (fun fic -> [ Cmd (S [ A "strip" ; P fic ]) ]) (fun s -> "pseudocode" / (env s)));

      rule "[%_finalize] perform a ln -s to the binary" 
        ~prod: "%_finalize" ~deps: [ "%.native" ]
        (rule_finalize "native" (fun _ -> []));

      rule "[%_finalize_bc] perform a ln -s to the binary" 
        ~prod: "%_finalize_bc" ~deps: [ "%.byte" ]
        (rule_finalize "byte" (fun _ -> []));
    end
  | _ -> ()
