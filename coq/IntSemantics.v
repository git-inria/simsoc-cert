(**
SimSoC-Cert, a Coq library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

.
*)

Require Import Bitvec.
Require Import State.
Require Import ZArith.
Require Import Integers. Import Int.
Require Import Coqlib.
Require Import Util.

Open Scope Z_scope.

Definition affect_reg (n : reg_num) (w : word) (b : bool)
  (s : state) : result :=
  Some(zne n 15, update_reg n w s).

Definition affect_reg_of_mode (n : reg_num) (w : word) 
  (m : processor_mode) (b : bool) (s : state) : result :=
  Some (b, update_reg n w
    (update_cpsr (update_bits 4 0 (mode_number m) (cpsr s)) s)).

Definition affect_cpsr (w : word) (b : bool) (s: state)
  : result := 
  Some(b, update_cpsr w s).

Definition affect_cpsr_bit (n : nat) (v w : word)(b : bool)
  (s: state) : result :=
  Some(b, update_cpsr (update_bit n v w) s).

Definition affect_cpsr_bits (n p : nat) (v w : word) (b : bool) (s : state)
  : result :=
  Some(b, update_cpsr (update_bits n p v w) s).

Definition affect_spsr (w : word) (m :option processor_exception_mode) 
  (b : bool) (s : state) : result :=
  Some(b, update_spsr m w s).

Definition intSeq (f1 f2 : (bool -> state -> result)) b1 s1 : result :=
  match f1 b1 s1 with
    | None => None
    | Some(b2, s2) =>
      match f2 b2 s2 with
        | None =>  None
        | Some (b3, s3) => Some(andb b2 b3, s3)
      end
  end.

Fixpoint intBlock (fs : list (bool->state->result)) b1 s1 :=
  match fs with
    | nil => Some (b1, s1)
    | f :: fs' =>
      match f b1 s1 with
        | None => None
        | Some(b2, s2) => intBlock fs' (andb b1 b2) s2
      end
  end.

Definition intIf (cond : bool) (f : (bool -> state -> result)) b s :=
      if cond then (f b s) else Some(b, s).

Definition intIfElse (cond : bool) (f1 f2 : (bool -> state -> result))
  b1 s1 :=
      if cond then f1 b1 s1 else f2 b1 s1.

Definition unpredictable (b : bool) (s : state) : result := None.
