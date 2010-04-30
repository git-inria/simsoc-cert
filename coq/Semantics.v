(**
SimSoC-Cert, a Coq library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Semantic functions for interpreting pseudo-code constructions.
*)

Require Import State Util Bitvec Arm State List String ZArith.

(****************************************************************************)
(** Result of executing an instruction.
The boolean in Ok indicates whether the PC needs to be incremented. *)
(****************************************************************************)

Inductive result : Type :=
| Ok (b : bool) (s : state)
| Ko (m : string)
| Todo (m : string).

Definition semfun := bool -> state -> result.

(****************************************************************************)
(** Semantic functions for pseudo-code constructions *)
(****************************************************************************)

Definition todo (m : string) (b : bool) (s : state) : result := Todo m.

Definition unpredictable (m : string) (b : bool) (s : state) : result := Ko m.

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

(****************************************************************************)
(** Semantic functions for the processor *)
(****************************************************************************)

Definition set_cpsr (v : word) (b : bool) (s: state) : result := 
  Ok b (set_cpsr s v).

Definition set_spsr (m : option exn_mode) (v : word) (b : bool) (s : state) :
  result := Ok b (set_spsr s m v).

Definition set_reg (n : regnum) (v : word) (b : bool) (s : state) : result
  := Ok (zne n 15) (set_reg s n v).

Definition set_reg_mode (m : proc_mode) (k : regnum) (v : word)
  (b : bool) (s : state) : result := Ok b (*FIXME?*) (set_reg_mode s m k v).

(****************************************************************************)
(** Semantic functions for the SCC and the memory *)
(****************************************************************************)

Definition write (a : address) (n : size) (w : word) (b : bool) (s : state) :
  result := Ok b (write s a n w).
