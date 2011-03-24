(**
SimSoC-Cert, a Coq library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the SH4 architecture following the:

SH-4, Software Manual, Renesas 32-Bit RISC, Rev.6.00 2006.09

Page numbers refer to Renesas_SH4_2006.pdf.

SH4 simulator.
*)

Set Implicit Arguments.

Require Import Semantics Sh4_Config Simul Bitvec Sh4_Functions Message.
Import Semantics.

(****************************************************************************)
(** Configuration *)
(****************************************************************************)

Module C <: CONFIG.

End C.

(****************************************************************************)
(** Simulator *)
(****************************************************************************)

Require sh4inst sh4dec.

Module _Semantics <: SEMANTICS _Sh4 _Sh4_State.
  Definition semstate := semstate.
  Definition result := @result.
  Definition semfun := semfun.
  Definition conjure_up_true := conjure_up_true.
  Definition inM := @inM.
  Definition ret := @ret.
  Definition incr_PC := incr_PC.
  Definition _get_st := @_get_st.
  Definition raise := @raise.
  Definition next := @next.
  Definition add_exn := add_exn.
End _Semantics.

Module _Functions <: FUNCTIONS _Sh4.
  Definition next := @Sh4_Functions.Decoder.next message.
End _Functions.

Module Import Simul := Simul.Make _Sh4 _Sh4_State _Semantics _Functions. (* COQFIX "The kernel does not recognize yet that a parameter can be instantiated by an inductive type." *)

Module I <: INST.
  Definition inst : Type := sh4inst.inst.
  Module S := sh4inst.InstSem C.
  Definition step : inst -> semfun unit := S.step.
  Definition decode : word -> decoder_result inst := sh4dec.decode.
  Definition handle_exception := Ok tt.
End I.

Module Export S := Simul.Make I.
