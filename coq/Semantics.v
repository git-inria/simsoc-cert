(**
SimSoC-Cert, a Coq library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Semantic functions for interpreting pseudo-code constructions.
*)

Require Import Arm_State Util Bitvec Arm List Message ZArith String.

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

(*Inductive map_sod : Type :=
  | mk_map_sod : forall i h l, sod_of_id i -> map_sod.
*)

Record map_sod : Type := mk_map_sod {
  id : nat;
  contents : single_or_double
}.

Definition local := list map_sod.

Record semstate := mk_semstate
  { loc : local
  ; bo : bool
  ; s0 : state
  ; st : state }.

Inductive result {A} : Type :=
| Ok (_ : A) (_ : semstate)
| Ko (m : message)
| Todo (m : message).

Definition semfun A := semstate -> @result A.

Definition ok_semstate {A} (a : A) loc bo s0 st := Ok a (mk_semstate loc bo s0 st).

Definition todo {A} (m : message) : semfun A := fun _ => Todo m.

Definition unpredictable {A} (m : message) : semfun A := fun _ => Ko m.

Definition if_then_else {A} (c : bool) (f1 f2 : semfun A) : semfun A := 
  if c then f1 else f2.

Definition if_then (c : bool) (f : semfun unit) : semfun unit :=
  if_then_else c f (Ok tt).

Definition if_CurrentModeHasSPSR {A} (f : exn_mode -> semfun A) : semfun A :=
  fun lb_s => 
  match mode (st lb_s) with
    | usr | sys => unpredictable EmptyMessage lb_s
    | exn em => f em lb_s
  end.

Definition return_ {A} (_ : word) : semfun A :=
  todo ComplexSemantics.

Definition memof (_: word) : word := repr 0. (* SH4 todo : C pointer *)
Definition addrof (_: word) : word := repr 0. (* SH4 todo : C pointer *)

Definition bind {A B} (m : semfun A) (f : A -> semfun B) : semfun B :=
  fun lbs0 => 
  match m lbs0 with 
    | Ok a lbs1 => f a lbs1
    | Ko m => Ko m
    | Todo m => Todo m
  end.

Notation "'do' X <- A ; B" := (bind A (fun X => B))
  (at level 200, X ident, A at level 100, B at level 200).

Definition seq {A B} (f1 : semfun A) (f2 : semfun B) : semfun B :=
  fun lbs0 =>
  match f1 lbs0 with
    | Ok a1 lbs1 =>
      match f2 lbs1 with
        | Ok a2 lbs2 => ok_semstate a2 (loc lbs2) (andb (bo lbs1) (bo lbs2)) (s0 lbs0) (st lbs2)
        | Ko m => Ko m
        | Todo m => Todo m
      end
      | Ko m => Ko m
      | Todo m => Todo m
  end.

Notation "'do_then' A ; B" := (seq A B)
  (at level 200 , A at level 100 , B at level 200).

Definition block l := List.fold_left seq l (Ok tt).

Fixpoint loop_aux (p k : nat) (f : nat -> semfun unit) : semfun unit :=
  fun lbs0 => 
  match k with
    | 0 => Ok tt lbs0
    | S k' =>
      match f p lbs0 with
        | Ok _ lbs1 => loop_aux (S p) k' f lbs1
        | r => r
      end
  end.

Definition loop (p q : nat) := loop_aux p (q - p + 1).

Fixpoint update_loc_aux (nb : nat) (v :single_or_double) (loc : local)
  : local :=
  match loc with
    | nil => mk_map_sod nb v :: loc
    | sod1 :: locs => if beq_nat nb (id sod1) then mk_map_sod nb v :: loc
      else sod1 :: update_loc_aux nb v locs
  end.

Definition update_loc_ V f (nb : nat) (v : V) : semfun unit :=
  fun lbs => ok_semstate tt (update_loc_aux nb (f v) (loc lbs)) (bo lbs) (s0 lbs) (st lbs).

Definition update_loc := update_loc_ word Single.
Definition update_loc64 := update_loc_ long Double.

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

Definition map_state f : semfun unit :=
  fun lbs => ok_semstate tt (loc lbs) (bo lbs) (s0 lbs) (f (st lbs)).

Definition set_cpsr v := map_state (fun st => set_cpsr st v).
Definition set_cpsr_bit n v := map_state (fun st => set_cpsr_bit st n v).
Definition set_spsr m v := map_state (fun st => set_spsr st m v).

Definition set_reg (n : regnum) (v : word) : semfun unit := 
  fun lbs => ok_semstate tt (loc lbs) (zne n 15) (s0 lbs) (set_reg (st lbs) n v).

Definition set_reg_mode m k v :=
  map_state (fun st => (*FIXME?*) set_reg_mode st m k v).
Definition write a n w := map_state (fun st => write st a n w).

Definition fExclusive f (addr : word) pid size := 
  map_state (fun st => f st addr (nat_of_Z pid)
    (nat_of_Z size)).

Definition MarkExclusiveGlobal := fExclusive MarkExclusiveGlobal.
Definition MarkExclusiveLocal := fExclusive MarkExclusiveLocal.
Definition ClearExclusiveByAddress := fExclusive ClearExclusiveByAddress.

Definition ClearExclusiveLocal pid :=
  map_state (fun st => ClearExclusiveLocal st (nat_of_Z pid)).

Definition IsExclusiveGlobal (s : state) (addr : word) (pid : word)
  (size : nat) : bool := false.

Definition IsExclusiveLocal (s : state) (addr : word) (pid : word)
  (size : nat) : bool := false.

Definition save_s0_true (lbs : semstate) :=
  let s := st lbs in
  ok_semstate tt nil true s s.

Definition save_s0_false (lbs : semstate) :=
  let s := st lbs in
  ok_semstate tt nil false s s.

Definition bind_s {A0} fs A (m : semfun unit) (f : A0 -> semfun A) : semfun A :=
  fun lbs0 => 
  match m lbs0 with 
    | Ok a lbs1 => f (fs lbs1) lbs1
    | Ko m => Ko m
    | Todo m => Todo m
  end.

Definition _get_s0 {A} := bind_s s0 A (Ok tt).
Definition _get_st {A} := bind_s st A (Ok tt).
Definition _get_loc {A} := bind_s loc A (Ok tt).
Definition _get_bo {A} := bind_s bo A (Ok tt).