(**
SimSoC-Cert, a Coq library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Semantic functions for interpreting pseudo-code constructions.
*)

Require Import State String Util Bitvec Arm State List.

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

Definition set_reg (n : regnum) (w : word) (b : bool) (s : state) : result
  := Ok (zne n 15) (set_reg s n w).

Definition set_reg_mode (m : proc_mode) (k : regnum) (w : word)
  (b : bool) (s : state) : result := Ok b (*FIXME?*) (set_reg_mode s m k w).

Definition set_cpsr (w : word) (b : bool) (s: state) : result := 
  Ok b (set_cpsr s w).

Definition set_cpsr_bit (n : nat) (v w : word) (b : bool) (s : state) : result
  := Ok b (State.set_cpsr s (update_bit n v w)).

Definition set_cpsr_bits (n p : nat) (v w : word) (b : bool) (s : state)
  : result := Ok b (State.set_cpsr s (update_bits n p v w)).

Definition set_spsr (m : option exn_mode) (w : word) (b : bool) (s : state)
  : result := Ok b (set_spsr s m w).

Definition seq (f1 f2 : bool->state->result) (b1 : bool) (s1 : state) : result
  := match f1 b1 s1 with
    | Ok b2 s2 =>
      match f2 b2 s2 with
        | Ok b3 s3 => Ok (andb b2 b3) s3
        | r => r
      end
    | r => r
  end.

Fixpoint block (fs : list (bool->state->result)) (b1 : bool) (s1 : state)
  : result :=
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
