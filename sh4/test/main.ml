let _ = (* this line with no OCaml side effect is here to be sure that ocamlbuild can compile the whole project with Sh4, without errors *)
  Sh4_Dec.decode, Sh4_Simul.S.simul
