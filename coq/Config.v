(**
SimSoC-Cert, a Coq library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Configuration of a ARM processor (IMPLEMENTATION DEFINED parameters).
*)

Set Implicit Arguments.

Require Import Bitvec.
Require Import ZArith.

(****************************************************************************)
(** Architecture versions (p. 13) *)
(****************************************************************************)

Inductive version : Type :=
(* All architecture names prior to ARMv4 are now OBSOLETE *)
| ARMv4 | ARMv4T
| ARMv5T | ARMv5TExP (*for legacy reasons only*) | ARMv5TE | ARMv5TEJ
| ARMv6.

(****************************************************************************)
(** A2.4.3 Reading the program counter (p. 47) *)
(****************************************************************************)

Inductive store_PC_offset_value : Type := O8 | O12.

Definition store_PC_offset (v : store_PC_offset_value) : word :=
  match v with
    | O8 => w8
    | O12 => w12
  end.
 
(****************************************************************************)
(** A2.6.5 Abort models (p. 61) *)
(****************************************************************************)

Inductive abort_model : Type := Restored | Updated.

(****************************************************************************)
(** All IMPLEMENTATION DEFINED parameters *)
(****************************************************************************)

(*FIXME: to be completed*)

Module Type CONFIG.

  (* Architecture versions (p. 13) *)
  Variable version : version.

  (* A2.4.3 Reading the program counter (p. 47) *)
  Variable store_PC_offset : store_PC_offset_value.

  (* A2.6 Exceptions (p. 54) *)
  Variable ve_irq_normal_address : Z.
  Variable ve_fiq_normal_address : Z.
  Variable ve_irq_high_vector_address : Z.
  Variable ve_fiq_high_vector_address : Z.

  (* A2.6.5 Abort models (p. 61) *)
  Variable abort_model : abort_model.

  (* A2.6.7 Imprecise data aborts (p. 61) *)
  Variable imprecise_aborts_max : Z.

  (* A2.7.3 Endian configuration and control (p. 72) *)
  Variable be32_support : bool.
  
  (* A4.1.7 BKPT (p. 164)*)
  Variable not_overridden_by_debug_hardware : bool.

  (* A2.6.11 High Vectors (p. 64)*)
  Variable high_vectors_configured : bool.

  (* A4.1.11 BXJ (p. 172)*)
  Variable JE_bit_of_Main_Configuration_register : Z.
  Variable CV_bit_of_Jazelle_OS_Control_register : Z.
  Variable SUBARCHITECTURE_DEFINED_value : word.
  Variable Jazelle_Extension_accepts_opcode_at_jpc : bool.
  Variable IMPLEMENTATION_DEFINED_CONDITION : bool.

  Variable get_CP15_reg1_EEbit : word.

End CONFIG.
