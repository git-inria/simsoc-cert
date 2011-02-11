(**
SimSoC-Cert, a Coq library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the SH4 architecture following the:

SH-4, Software Manual, Renesas 32-Bit RISC, Rev.6.00 2006.09

Page numbers refer to Renesas_SH4_2006.pdf.

Semantic functions for interpreting pseudo-code constructions.
*)

Require Import Sh4_State Util Bitvec Sh4 List Message ZArith String.

(****************************************************************************)
(** Semantic functions for pseudo-code constructions and processor
 ** with a list of variables*)
(****************************************************************************)

Inductive single_or_double : Type :=
| Single : word -> single_or_double
| Double :long -> single_or_double.

Notation id_result := (S (S (S (S 0)))).
Notation id_value := 0.

Definition sod_of_id (i : nat) :=
  match i with
    | id_result (*result*) => long -> single_or_double
    | id_value (*value*) => long -> single_or_double
    | _ => word -> single_or_double
  end.

Record map_sod : Type := mk_map_sod {
  id : nat;
  contents : single_or_double
}.

Definition local := list map_sod.

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

Definition return_ (_ : word) (loc : local)
  (b : bool) (s : state) : result :=
  todo ComplexSemantics loc b s.

Definition memof (_: word) : word := repr 0. (* SH4 todo : C pointer *)
Definition addrof (_: word) : word := repr 0. (* SH4 todo : C pointer *)

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

Fixpoint update_loc_aux (nb : nat) (v :single_or_double) (loc : local)
  : local :=
  match loc with
    | nil => mk_map_sod nb v :: loc
    | sod1 :: locs => if beq_nat nb (id sod1) then mk_map_sod nb v :: loc
      else sod1 :: update_loc_aux nb v locs
  end.

Definition update_loc (nb : nat) (v : word) (loc : local)
  (b : bool) (s : state) : result :=
  Ok (update_loc_aux nb (Single v) loc) b s.

Definition update_loc64 (nb : nat) (v : long) (loc : local)
  (b : bool) (s : state) : result :=
  Ok (update_loc_aux nb (Double v) loc) b s.

Fixpoint get_loc_aux (nb : nat) (loc : local) :=
  match loc with
    | nil => Single zero
    | sod1 :: locs => if beq_nat nb (id sod1) then (contents sod1)
      else get_loc_aux nb locs
  end.

Definition get_loc (nb : nat) (loc : local) :=
  match (get_loc_aux nb loc) with
    | Single v => v
    | Double v => Word.repr (sbits64 31 0 v)
  end.

Definition get_loc64 (nb : nat) (loc : local) :=
  match (get_loc_aux nb loc) with
    | Single v => to64 w0 v
    | Double v => v
  end.

Definition set_cpsr (v : word) (loc : local) (b : bool) 
  (s: state) : result :=
  Ok loc b (set_cpsr s v).

Definition set_cpsr_bit (n : nat) (v : word) (loc : local)
  (b : bool) (s: state) : result :=
  Ok loc b (set_cpsr_bit s n v).

Definition set_reg (n : regnum) (v : word) 
  (loc : local) (b : bool) (s : state) : result
  := Ok loc (zne n 15) (set_reg s n v).
