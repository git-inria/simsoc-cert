(**
SimSoC-Cert, a Coq library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Semantic functions for interpreting pseudo-code constructions.
*)

Require Import State Util Bitvec Arm State List Message ZArith String.

(****************************************************************************)
(** Semantic functions for pseudo-code constructions and processor
 ** with a list of variables*)
(****************************************************************************)

Definition local := list (nat * word).

Inductive result : Type :=
| Ok (loc : local) (b : bool) (s : state)
| Ko (m : message)
| Todo (m : message).

Definition semfun := local -> bool -> state -> result.

Definition todo (m : message) (loc : local) (b : bool) 
  (s : state) : result := Todo m.

Definition unpredictable (m : message) (loc : local) 
  (b : bool) (s : state) : result := Ko m.

Definition if_then (c : bool) (f : semfun) (loc : local)
  (b : bool) (s : state) : result :=
  if c then f loc b s else Ok loc b s.

Definition if_then_else (c : bool) (f1 f2 : semfun) 
  (loc : local) (b : bool) (s : state)
  : result := if c then f1 loc b s else f2 loc b s.

Definition if_CurrentModeHasSPSR (f : exn_mode -> semfun)
  (loc : local) (b : bool) (s : state) : result :=
  match mode s with
    | usr | sys => unpredictable EmptyMessage loc b s
    | exn em => f em loc b s
  end.

Definition seq (f1 f2 : semfun) (loc0 : local) 
  (b0 : bool) (s0 : state) : result :=
  match f1 loc0 b0 s0 with
    | Ok loc1 b1 s1 =>
      match f2 loc1 b1 s1 with
        | Ok loc2 b2 s2 => Ok loc2 (andb b1 b2) s2
        | r => r
      end
    | r => r
  end.

Fixpoint block (fs : list semfun) (loc0 : local) (b0 : bool) 
  (s0 : state) : result :=
  match fs with
    | nil => Ok loc0 b0 s0
    | f :: fs' =>
      match f loc0 b0 s0 with
        | Ok loc1 b1 s1 => block fs' loc1 (andb b0 b1) s1
        | r => r
      end
  end.

Fixpoint loop_aux (p k : nat) (f : nat -> semfun) 
  (loc0 : local) (b0 : bool) (s0 : state)
  : result :=
  match k with
    | 0 => Ok loc0 b0 s0
    | S k' =>
      match f p loc0 b0 s0 with
        | Ok loc1 b1 s1 => loop_aux (S p) k' f loc1 b1 s1
        | r => r
      end
  end.

Definition loop (p q : nat) (f : nat -> semfun) (loc0 : local)
  (b0 : bool) (s0 : state)
  : result := loop_aux p (q - p + 1) f loc0 b0 s0.

Fixpoint update_loc_aux (nb : nat) (v : word) (loc : local)
  : local :=
  match loc with
    | nil => ((List.length loc +1, v) :: loc)
    | (nb', v') :: locs => if eq nb nb' then (nb, v) :: locs 
      else (nb', v') :: update_loc_aux nb v locs
  end.

Definition update_loc (nb : nat) (v : word) (loc : local)
  (b : bool) (s : state) : result :=
  Ok (update_loc_aux nb v loc) b s.

(*Fixpoint get_loc (str : string) (loc : local) : word :=
  match loc with
    | nil => zero
    | (s, v) :: locs => if string_dec s str then v else get_loc str locs
  end.*)

Fixpoint get_loc (nb : nat) (loc : local) : word :=
  match loc with
    | nil => zero
    | (nb', v) :: locs => if eq nb nb' then v else get_loc nb locs
  end.

Definition set_cpsr (v : word) (loc : local) (b : bool) 
  (s: state) : result :=
  Ok loc b (set_cpsr s v).

Definition set_cpsr_bit (n : nat) (v : word) (loc : local)
  (b : bool) (s: state) : result :=
  Ok loc b (set_cpsr_bit s n v).

Definition set_spsr (m : exn_mode) (v : word) 
  (loc : local) (b : bool) (s : state) :
  result := Ok loc b (set_spsr s m v).

Definition set_reg (n : regnum) (v : word) 
  (loc : local) (b : bool) (s : state) : result
  := Ok loc (zne n 15) (set_reg s n v).

Definition set_reg_mode (m : proc_mode) (k : regnum) (v : word)
  (loc : local) (b : bool) (s : state) : 
  result := Ok loc b (*FIXME?*) (set_reg_mode s m k v).

Definition write (a : word) (n : size) (w : word) 
  (loc : local) (b : bool) (s : state) :
  result := Ok loc b (write s a n w).

Definition MarkExclusiveGlobal (addr : word) (pid : word) (size : word)
  (loc : local) (b : bool) (s : state) : result :=
  Ok loc b (MarkExclusiveGlobal s addr (nat_of_Z pid)
    (nat_of_Z size)).

Definition MarkExclusiveLocal (addr : word) (pid : word) (size : word)
  (loc : local) (b : bool) (s : state) : result :=
  Ok loc b (MarkExclusiveLocal s addr (nat_of_Z pid) 
    (nat_of_Z size)).

Definition ClearExclusiveByAddress (addr: word) (pid : word) (size : word)
  (loc : local) (b : bool) (s : state) : result :=
  Ok loc b (ClearExclusiveByAddress s addr (nat_of_Z pid) (nat_of_Z size)).

Definition ClearExclusiveLocal (pid : word) (loc : local)
  (b : bool) (s : state) : result :=
  Ok loc b (ClearExclusiveLocal s (nat_of_Z pid)).

Definition IsExclusiveGlobal (s : state) (addr : word) (pid : word)
  (size : nat) : bool := false.

Definition IsExclusiveLocal (s : state) (addr : word) (pid : word)
  (size : nat) : bool := false.
