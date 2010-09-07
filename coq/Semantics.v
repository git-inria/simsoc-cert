(**
SimSoC-Cert, a Coq library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Semantic functions for interpreting pseudo-code constructions.
*)

Require Import State Util Bitvec Arm State List Message ZArith.

(****************************************************************************)
(** Result of executing an instruction.
The boolean in Ok indicates whether the PC needs to be incremented. *)
(****************************************************************************)

Inductive result : Type :=
| Ok (b : bool) (s : state)
| Ko (m : message)
| Todo (m : message).

Definition semfun := bool -> state -> result.

(****************************************************************************)
(** Semantic functions for pseudo-code constructions *)
(****************************************************************************)

Definition todo (m : message) (b : bool) (s : state) : result := Todo m.

Definition unpredictable (m : message) (b : bool) (s : state) : result := Ko m.

Definition if_then (c : bool) (f : semfun) (b : bool) (s : state) : result :=
  if c then f b s else Ok b s.

Definition if_then_else (c : bool) (f1 f2 : semfun) (b : bool) (s : state)
  : result := if c then f1 b s else f2 b s.

Definition seq (f1 f2 : semfun) (b0 : bool) (s0 : state) : result :=
  match f1 b0 s0 with
    | Ok b1 s1 =>
      match f2 b1 s1 with
        | Ok b2 s2 => Ok (andb b1 b2) s2
        | r => r
      end
    | r => r
  end.

Fixpoint block (fs : list semfun) (b0 : bool) (s0 : state) : result :=
  match fs with
    | nil => Ok b0 s0
    | f :: fs' =>
      match f b0 s0 with
        | Ok b1 s1 => block fs' (andb b0 b1) s1
        | r => r
      end
  end.

Fixpoint loop_aux (p k : nat) (f : nat -> semfun) (b0 : bool) (s0 : state)
  : result :=
  match k with
    | 0 => Ok b0 s0
    | S k' =>
      match f p b0 s0 with
        | Ok b1 s1 => loop_aux (S p) k' f b1 s1
        | r => r
      end
  end.

Definition loop (p q : nat) (f : nat -> semfun) (b0 : bool) (s0 : state)
  : result := loop_aux p (q - p + 1) f b0 s0.

(****************************************************************************)
(** Semantic functions for the processor *)
(****************************************************************************)

Definition set_cpsr (v : word) (b : bool) (s: state) : result :=
  Ok b (set_cpsr s v).

Definition set_cpsr_bit (n : nat) (v : word) (b : bool) (s: state) : result :=
  Ok b (set_cpsr_bit s n v).

Definition set_spsr (m : option exn_mode) (v : word) (b : bool) (s : state) :
  result := Ok b (set_spsr s m v).

Definition set_reg (n : regnum) (v : word) (b : bool) (s : state) : result
  := Ok (zne n 15) (set_reg s n v).

Definition set_reg_mode (m : proc_mode) (k : regnum) (v : word)
  (b : bool) (s : state) : result := Ok b (*FIXME?*) (set_reg_mode s m k v).

(****************************************************************************)
(** Semantic functions for the SCC and the memory *)
(****************************************************************************)

Definition write (a : word) (n : size) (w : word) (b : bool) (s : state) :
  result := Ok b (write s a n w).

Definition MarkExclusiveGlobal (addr : word) (pid : nat) (size : nat)
  (b : bool) (s : state) : result :=
  Ok b (MarkExclusiveGlobal s addr pid size).

Definition MarkExclusiveLocal (addr : word) (pid : nat) (size : nat)
  (b : bool) (s : state) : result :=
  Ok b (MarkExclusiveLocal s addr pid size).

Definition ClearExclusiveByAddress (addr: word) (pid : nat) (size : nat)
  (b : bool) (s : state) : result :=
  Ok b (ClearExclusiveByAddress s addr pid size).

Definition ClearExclusiveLocal (pid : nat) (b : bool) (s : state) : result :=
  Ok b (ClearExclusiveLocal s pid).
