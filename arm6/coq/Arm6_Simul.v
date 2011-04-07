(**
SimSoC-Cert, a toolkit for generating certified processor simulators.

See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

ARM simulator.
*)

Set Implicit Arguments.

Require Import Semantics Arm_Config Simul Bitvec Arm_Functions.
Import Arm_Functions.Semantics.

(****************************************************************************)
(** Configuration *)
(****************************************************************************)

Module C <: CONFIG.

  (* A2.4.3 Reading the program counter (p. 47) *)
  Definition store_PC_offset : store_PC_offset_value := O8.

  (* A2.6 Exceptions (p. 54) *)
  Definition VE_IRQ_address : word := w0.
  Definition VE_FIQ_address : word := w0.

  (* A2.7.3 Endian configuration and control (p. 72) *)
  Definition BE32_support : bool := false.
  
  (* A4.1.7 BKPT (p. 164) *)
  Definition not_overridden_by_debug_hardware : bool := true.

  (* A4.1.11 BXJ (p. 172) *)
  Definition JE_bit_of_Main_Configuration_register : bool := false.
  Definition CV_bit_of_Jazelle_OS_Control_register : bool := false.
  Definition jpc_SUB_ARCHITECTURE_DEFINED_value : word := w0.
  Definition invalidhandler_SUB_ARCHITECTURE_DEFINED_value : word := w0.
  Definition Jazelle_Extension_accepts_opcode_at (jpc : word) := true.
  Definition IMPLEMENTATION_DEFINED_CONDITION : bool := true.

End C.

(****************************************************************************)
(** Simulator *)
(****************************************************************************)

Require arm6inst arm6dec Arm_Exception.

Module _Semantics <: SEMANTICS _Arm _Arm_State _Arm_Message.
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
  Module Decoder_result := Decoder_result.
End _Semantics.

Module _Functions <: FUNCTIONS _Arm _Arm_Message.
  Definition next := @Arm_Functions.Semantics.Decoder.next.
End _Functions.

Module Import Simu := Simul.Make _Arm _Arm_State _Arm_Message _Semantics _Functions. (* COQFIX "The kernel does not recognize yet that a parameter can be instantiated by an inductive type." *)
(* COQFIX The line "Module Import Simul" would import the file Simul.v (in the absence of the scope SimSoCCert) instead of the dynamically being created one. *)
Module I <: INST.
  Definition inst : Type := arm6inst.inst.
  Module S := arm6inst.InstSem C.
  Definition step : inst -> semfun unit := S.step.
  Definition decode : word -> decoder_result inst := arm6dec.decode.
  Module E := Arm_Exception.InstSem C.
  Definition handle_exception : semfun unit := E.step.
End I.

Module Export S := Simu.Make I.
