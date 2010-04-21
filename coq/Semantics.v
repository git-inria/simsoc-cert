(**
SimSoC-Cert, a Coq library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Semantic functions for interpreting pseudo-code constructions.
*)

Require Import State String Util Bitvec Proc State List.

(****************************************************************************)
(** Result of executing an instruction.
The boolean indicates whether the PC needs to be incremented. *)
(****************************************************************************)

Inductive result : Type :=
| Ok (b : bool) (s : state)
| Ko (m : string)
| Todo (m : string).

(****************************************************************************)
(** Semantics functions for pseudo-code constructions *)
(****************************************************************************)

Definition affect_reg (n : regnum) (w : word) (b : bool) (s : state) : result
  := Ok (zne n 15) (update_reg n w s).

Definition affect_reg_of_mode (n : regnum) (w : word) (m : processor_mode)
  (b : bool) (s : state) : result := (*FIXME*)
  Ok b (update_reg n w
    (update_cpsr (update_bits 4 0 (word_of_processor_mode m) (cpsr (proc s))) s)).

Definition affect_cpsr (w : word) (b : bool) (s: state) : result := 
  Ok b (update_cpsr w s).

Definition affect_cpsr_bit (n : nat) (v w : word) (b : bool) (s : state)
  : result := Ok b (update_cpsr (update_bit n v w) s).

Definition affect_cpsr_bits (n p : nat) (v w : word) (b : bool) (s : state)
  : result := Ok b (update_cpsr (update_bits n p v w) s).

Definition affect_spsr (w : word) (m : option processor_exception_mode) 
  (b : bool) (s : state) : result := Ok b (update_spsr m w s).

Definition seq (f1 f2 : bool->state->result) b1 s1 : result :=
  match f1 b1 s1 with
    | Ok b2 s2 =>
      match f2 b2 s2 with
        | Ok b3 s3 => Ok (andb b2 b3) s3
        | r => r
      end
    | r => r
  end.

Fixpoint block (fs : list (bool->state->result)) b1 s1 :=
  match fs with
    | nil => Ok b1 s1
    | f :: fs' =>
      match f b1 s1 with
        | Ok b2 s2 => block fs' (andb b1 b2) s2
        | r => r
      end
  end.

Definition if_then (c : bool) (f : bool->state->result) b s :=
  if c then f b s else Ok b s.

Definition if_then_else (c : bool) (f1 f2 : bool->state->result) b1 s1 :=
  if c then f1 b1 s1 else f2 b1 s1.

Definition unpredictable (m : string) (b : bool) (s : state) : result :=
  Ko m.

Definition todo (m : string) (b : bool) (s : state) : result :=
  Todo m.

(****************************************************************************)
(** Other semantic functions *)
(****************************************************************************)

Definition Start_opcode_execution_at (w : word) (b : bool) (s : state)
  : result := Ok b s. (*FIXME*)
