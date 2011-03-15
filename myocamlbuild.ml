module Ocamlbuild_plugin = 
struct
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
          f After_rules
        end
      | x -> f x
end

open Ocamlbuild_plugin

let ln_s src dest = 
  if Sys.file_exists dest then
    Nop
  else
    ln_s src dest

let arch = "arm"
let variant = "linux"

let l_compcert = List.map ((/) "compcert")
  [ "lib" ; "common" ; arch / variant ; arch ; "backend" ; "cfrontend" ; "driver" 
  ; "extraction" ]

let path = 
  let open Pathname in 
  concat parent_dir_name

(*
let rule_finalize dir fic l_cmd = 
  let dir_fic = sprintf "%s/%s" dir fic in
  rule (sprintf "[%s/finalize] strip and ln -s" dir)
    ~prod: (sprintf "%s/finalize" dir) ~deps: [ sprintf "%s.native" dir_fic ]
    (fun _ _ -> Seq ( ln_s (sprintf "../_build/%s.native" dir_fic) (let open Pathname in concat parent_dir_name dir_fic)
                      (* FIXME find a more generical way to create this symbolic link *)
                      :: l_cmd dir_fic))
*)  

let _ = dispatch & function
(*
  | Before_options ->
    Options.ocamlopt := S (A "ocamlopt" :: 
                             List.map (fun x -> Sh x) [ "-unsafe"; "-noassert" ; "-inline 10000"])
*)

  | After_rules ->
    begin
      (* force linking of libCparser.a when use_Cparser is set *)
      flag ["link"; "ocaml"; "native"; "use_Cparser"]
        (S[A"compcert/cfrontend/libCparser.a"]);
      flag ["link"; "ocaml"; "byte"; "use_Cparser"]
        (S[A"-custom"; A"compcert/cfrontend/libCparser.a"]);
      
      (* make sure libCparser.a is up to date *)
      dep  ["link"; "ocaml"; "use_Cparser"] ["compcert/cfrontend/libCparser.a"];

      List.iter (fun x -> Pathname.define_context x ("compcert" :: (* The directory [compcert/cfrontend] needs to have a relative path notion to [cparser], but [cparser] is inside [compcert], so we have to add [compcert]. *)
                                                        l_compcert)) l_compcert;
      Pathname.define_context "sh4" [ "compcert/cfrontend" (* we just use the library [Cparser] which is virtually inside [cfrontend] *) ; "sh4" ];
      Pathname.define_context "extract/tmp" [ "compcert/extraction" ; "extract/tmp" ];
      Pathname.define_context "pseudocode" (l_compcert @ [ "extract/tmp" ; "sh4" ; "refARMparsing" ; "pseudocode" ]);

      rule "[sh4/finalize] strip and ln -s" 
        ~prod: "sh4/finalize" ~deps: [ "sh4/instr.native" ]
        (fun _ _ -> Seq [ ln_s "../_build/sh4/instr.native" (let open Pathname in 
                                                                   concat parent_dir_name "sh4/instr")
                          (* FIXME find a more generical way to create this symbolic link *) ]);

      rule "[pseudocode/finalize] strip and ln -s" 
        ~prod: "pseudocode/finalize" ~deps: [ "pseudocode/main.native" ]
        (fun _ _ -> Seq [ ln_s "../_build/pseudocode/main.native" (let open Pathname in 
                                                                   concat parent_dir_name "pseudocode/main")
                          (* FIXME find a more generical way to create this symbolic link *)
                        ; Cmd (S [A "strip" ; P ("pseudocode/main.native") ]) ]);
(*
      rule_finalize "sh4" "instr" (fun _ -> []);
      rule_finalize "pseudocode" "main" (fun dir_fic -> [ Cmd (S [A "strip" ; P (sprintf "%s.native" dir_fic) ])])
*)
    end
  | _ -> ()
