(**
SimSoC-Cert, a Coq library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Instruction decoding and execution cycle.
*)

Set Implicit Arguments.

Require Import Bitvec Arm Semantics Arm_State Message.
Require Recdef.

(****************************************************************************)
(** decoding result type *)
(****************************************************************************)

Section decoder_result.

 Variable inst : Type.

 Inductive decoder_result : Type :=
 | DecInst : inst -> decoder_result
 | DecUnpredictable : decoder_result
 | DecError : message -> decoder_result
 | DecUndefined_with_num : nat -> decoder_result.

Notation DecUndefined := (DecUndefined_with_num 0).

End decoder_result.

Definition decode_cond (w : word) (inst : Type) (g : opcode -> inst) :
  decoder_result inst :=
  match condition w with
    | Some oc => DecInst (g oc)
    | None => @DecUndefined_with_num inst 1
  end.

Definition decode_cond_mode (mode : Type) (f : word -> decoder_result mode)
  (w : word) (inst : Type) (g : mode -> opcode -> inst) :
  decoder_result inst :=
  match condition w with
    | Some oc =>
      match f w with
        | DecInst i => DecInst (g i oc)
        | DecError m => @DecError inst m
        | DecUnpredictable => @DecUnpredictable inst
        | DecUndefined => @DecUndefined_with_num inst 2
      end
    | None => @DecUndefined_with_num inst 3
  end.

Definition decode_mode (mode : Type) (f : word -> decoder_result mode)
  (w : word) (inst : Type) (g : mode -> inst) :
  decoder_result inst :=
  match f w with
    | DecInst i => DecInst (g i)
    | DecError m => @DecError inst m
    | DecUnpredictable => @DecUnpredictable inst
    | DecUndefined => @DecUndefined_with_num inst 2
  end.

(****************************************************************************)
(** types and functions necessary for building a simulator *)
(****************************************************************************)

Module Type INST.
  Variable inst : Type.
  Variable step : inst -> semfun unit.
  Variable decode : word -> decoder_result inst.
  Variable handle_exception : semfun unit.
End INST.

(****************************************************************************)
(** functor building a simulator *)
(****************************************************************************)

(* b true means that the last instruction executed was not a jump *)
(* Because the PC register contains the address of the current instruction
 * plus 8 (cf A2.4.3), we add 8 to the PC if a jump occured (b false) *)
(* The implementation assumes that the processor is in ARM mode *)
Definition incr_PC_ARM (b: bool) (s : state) : state :=
  set_reg s PC (add (reg_content s PC) (repr (if b then 4 else 8))).

Record simul_state := mk_simul_state
  { semst : semstate
  ; nb_next : nat }.

Inductive simul_result {A} : Type :=
| SimOk : A -> simul_state -> simul_result
| SimKo : simul_state (* state before the current instruction *)
  -> message (* error message *) -> simul_result.

Definition simul_semfun A := simul_state -> @simul_result A.

Definition bind {A B} (m : simul_semfun A) (f : A -> simul_semfun B) : simul_semfun B :=
  fun lbs0 => 
  match m lbs0 with 
    | SimOk a lbs1 => f a lbs1
    | SimKo lbs m => SimKo lbs m
  end.

Notation "'do' X <- A ; B" := (bind A (fun X => B))
  (at level 200, X ident, A at level 100, B at level 200).

Definition catch {A} (m : simul_semfun A) (f : _ -> simul_semfun A) : simul_semfun A :=
  fun lbs0 => 
  match m lbs0 with 
    | SimKo lbs m => f m lbs
    | x => x
  end.

Definition bind_s fs A (m : simul_semfun unit) (f : state -> simul_semfun A) : simul_semfun A :=
  bind m (fun _ lbs1 => f (fs lbs1) lbs1).

Definition next {A B} (f1 : simul_semfun A) (f2 : simul_semfun B) : simul_semfun B :=
  do _ <- f1; f2.

Definition _get_st {A} := @bind_s (fun x => st (semst x)) A (SimOk tt).

Notation "'<' st '>' A" := (_get_st (fun st => A)) (at level 200, A at level 100, st ident).

Definition conjure_up_true (lbs : simul_state) :=
  SimOk tt (mk_simul_state (mk_semstate nil true (st (semst lbs))) (nb_next lbs)).

Module Make (Import I : INST).

  Definition handle_exception : simul_semfun unit :=
    fun lbs => 
      match handle_exception (semst lbs) with
      | Ok a lbs' => SimOk a (mk_simul_state lbs' (nb_next lbs))
      | Ko m | Todo m => SimKo lbs m
    end.

  Definition next : simul_semfun unit := <s>
    fun lbs => match inst_set (cpsr s) with
      | None => SimKo lbs InvalidInstructionSet
      | Some Jazelle => SimKo lbs JazelleInstructionSetNotImplemented
      | Some Thumb => SimKo lbs ThumbInstructionSetNotImplemented
      | Some ARM =>
        let a := address_of_current_instruction s in
        let w := read s a Word in
          match decode w with
            | DecError m => SimKo lbs m
            | DecUnpredictable => SimKo lbs DecodingReturnsUnpredictable
            | DecUndefined_with_num fake => handle_exception (mk_simul_state (let lbs := semst lbs in mk_semstate (loc lbs) (bo lbs) (add_exn s UndIns)) (nb_next lbs))
            | DecInst i =>
              match step i (semst lbs) with
                | Ok _ lbs' => handle_exception (mk_simul_state (mk_semstate (loc lbs') (bo lbs') (incr_PC_ARM (bo lbs') (st lbs'))) (nb_next lbs))
                | Ko m | Todo m => SimKo lbs m
              end
          end
    end.

  Function simul (lbs : simul_state) {measure nb_next lbs} : @simul_result unit :=
    match nb_next lbs with
      | 0%nat => SimOk tt lbs
      | S n' =>
        match next lbs with
          | SimOk _ s' => simul (mk_simul_state (semst s') n')
          | SimKo s m => SimKo s m
        end
    end.
    unfold nb_next.
    auto with *.
  Defined.

End Make.
