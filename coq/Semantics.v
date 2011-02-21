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
  ; st : state }.

Inductive result {A} : Type :=
| Ok (_ : A) (_ : semstate)
| Ko (m : message)
| Todo (m : message).

Definition semfun A := semstate -> @result A.

Definition ok_semstate {A} (a : A) loc bo st := Ok a (mk_semstate loc bo st).

Definition todo {A} (m : message) : semfun A := fun _ => Todo m.

Definition unpredictable {A} (m : message) : semfun A := fun _ => Ko m.

Definition if_then_else {A} (c : bool) (f1 f2 : semfun A) : semfun A := 
  if c then f1 else f2.

Notation "'If' A 'then' B 'else' C" := (if_then_else A B C) (at level 200).

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

Definition bind2 {A B C} (f : semfun (A * B)) (g : A -> B -> semfun C) : semfun C :=
  bind f (fun xy => g (fst xy) (snd xy)).

Notation "'do' ( X , Y ) <- A ; B" := (bind2 A (fun X Y => B))
   (at level 200, X ident, Y ident, A at level 100, B at level 200).

Definition ret {A} := @Ok A.

Definition next {A B} (f1 : semfun A) (f2 : semfun B) : semfun B :=
  do _ <- f1; f2.

Notation "'do_then' A ; B" := (next A B)
  (at level 200 , A at level 100 , B at level 200).

Definition bind_s {A} fs B (m : semfun unit) (f : A -> semfun B) : semfun B :=
  bind m (fun _ lbs1 => f (fs lbs1) lbs1).

Definition _get_loc {A} := bind_s loc A (Ok tt).
Definition _get_bo {A} := bind_s bo A (Ok tt).
Definition _get_st {A} := bind_s st A (Ok tt).

Notation "'<.' loc '.>' A" := (_get_loc (fun loc => A)) (at level 200, A at level 100, loc ident).
Notation "'<' st '>' A" := (_get_st (fun st => A)) (at level 200, A at level 100, st ident).
Notation "'<:' loc st ':>' A" := (<.loc.> <st> A) (at level 200, A at level 100, loc ident, st ident).

Definition _set_loc loc lbs := ok_semstate tt loc (bo lbs) (st lbs).
Definition _set_bo b lbs := ok_semstate tt (loc lbs) b (st lbs).
Definition _set_st st lbs := ok_semstate tt (loc lbs) (bo lbs) st.

Definition block (l : list (semfun unit)) : semfun unit := 
  let next_bo f1 f2 := next f1 (_get_bo f2) in
  List.fold_left (fun f1 f2 =>
    next_bo f1 (fun b1 => 
    next_bo f2 (fun b2 => _set_bo (andb b1 b2))) ) l (Ok tt).

Notation "[ ]" := (block nil).
Notation "[ a ; .. ; b ]" := (block (a :: .. (b :: nil) ..)).

Fixpoint loop_aux (p k : nat) (f : nat -> semfun unit) : semfun unit :=
  match k with
    | 0 => ret tt
    | S k' =>
    do_then f p ;
    loop_aux (S p) k' f
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
  <.loc.> _set_loc (update_loc_aux nb (f v) loc).

Definition update_loc := update_loc_ word Single.
Definition update_loc64 := update_loc_ long Double.

Fixpoint get_loc_aux (nb : nat) (loc : local) :=
  match loc with
    | nil => Single zero
    | sod1 :: locs => if beq_nat nb (id sod1) then (contents sod1)
      else get_loc_aux nb locs
  end.

Definition get_loc (nb : nat) (loc : local) :=
  match get_loc_aux nb loc with
    | Single v => v
    | Double v => Word.repr (sbits64 31 0 v)
  end.

Definition get_loc64 (nb : nat) (loc : local) :=
  match get_loc_aux nb loc with
    | Single v => to64 w0 v
    | Double v => v
  end.

Definition map_st f : semfun unit :=
  <st> _set_st (f st).

Definition set_cpsr v := map_st (fun st => set_cpsr st v).
Definition set_cpsr_bit n v := map_st (fun st => set_cpsr_bit st n v).
Definition set_spsr m v := map_st (fun st => set_spsr st m v).

Definition set_reg (n : regnum) (v : word) : semfun unit := 
  fun lbs => ok_semstate tt (loc lbs) (zne n 15) (set_reg (st lbs) n v).

Definition set_reg_mode m k v :=
  map_st (fun st => (*FIXME?*) set_reg_mode st m k v).
Definition write a n w := map_st (fun st => write st a n w).

Definition fExclusive f (addr : word) pid size := 
  map_st (fun st => f st addr (nat_of_Z pid)
    (nat_of_Z size)).

Definition MarkExclusiveGlobal := fExclusive MarkExclusiveGlobal.
Definition MarkExclusiveLocal := fExclusive MarkExclusiveLocal.
Definition ClearExclusiveByAddress := fExclusive ClearExclusiveByAddress.

Definition ClearExclusiveLocal pid :=
  map_st (fun st => ClearExclusiveLocal st (nat_of_Z pid)).

Definition IsExclusiveGlobal (s : state) (addr : word) (pid : word)
  (size : nat) : bool := false.

Definition IsExclusiveLocal (s : state) (addr : word) (pid : word)
  (size : nat) : bool := false.

Definition conjure_up_true (lbs : semstate) :=
  ok_semstate tt nil true (st lbs).

Definition conjure_up_false (lbs : semstate) :=
  ok_semstate tt nil false (st lbs).
