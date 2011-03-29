(**
SimSoC-Cert, a toolkit for generating certified processor simulators
See the COPYRIGHTS and LICENSE files.

Coq functor building a simulator given the semantics of instructions
*)

Set Implicit Arguments.

Require Import Bitvec Semantics Message.
Require Recdef.

Module Type SEMANTICS (Import P : PROC) (Import S : STATE P).
  Parameter semstate : Set.
  Parameter result : Type -> Type.
  Definition semfun A := semstate -> @result A.

  Parameter conjure_up_true : semfun unit.
  Parameter inM : forall A B : Type, (A -> semstate -> B) -> (message -> B) -> result A -> B.
  Parameter ret : forall A : Type, A -> semfun A.
  Parameter incr_PC : semfun unit.
  Parameter _get_st : forall A : Type, (state -> semfun A) -> semfun A.
  Parameter raise : forall A : Type, message -> semfun A.
  Parameter next : forall A B : Type, semfun A -> semfun B -> semfun B.
  Parameter add_exn : exception -> semfun unit.
End SEMANTICS.

Module Type FUNCTIONS (Import P : PROC).
  Parameter next : forall A, (message -> A) -> A -> instruction_set -> A.
End FUNCTIONS.

(****************************************************************************)
(** functor building a simulator *)
(****************************************************************************)

Module Make (Import P : PROC) (Import S : STATE P) (Import Sem : SEMANTICS P S) (F : FUNCTIONS P).

  (****************************************************************************)
  (** types and functions necessary for building a simulator *)
  (****************************************************************************)

  Notation "'do_then' A ; B" := (next A B)
    (at level 200 , A at level 100 , B at level 200).

  Module Type INST.
    Variable inst : Type.
    Variable step : inst -> semfun unit.
    Variable decode : word -> decoder_result inst.
    Variable handle_exception : semfun unit.
  End INST.

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

  Notation "'<' st '>' A" := (_get_st (fun st => A)) (at level 200, A at level 100, st ident).

  Definition inM {A} (m : semfun A) : simul_semfun A :=
    fun lbs => 
    inM 
      (fun a lbs' => SimOk a (mk_simul_state lbs' (nb_next lbs))) 
      (SimKo lbs) 
      (m (semst lbs)).

  Definition conjure_up_true := inM conjure_up_true.

  Definition error {A} x lbs := @SimKo A lbs x.

  Module Make (Import I : INST).

    Definition raise {A} := raise A.

    Definition next : semfun unit := <s>
      match inst_set (cpsr s) with
        | None => raise InvalidInstructionSet
        | Some x => 
          F.next raise (
          let a := address_of_current_instruction s in
          let w := read s a Word in
            match decode w with
              | DecError m => raise m
              | DecUnpredictable => raise DecodingReturnsUnpredictable
              | DecUndefined_with_num fake => 
                  do_then add_exn UndIns;
                  handle_exception
              | DecInst i =>
                  do_then step i;
                  do_then incr_PC;
                  handle_exception
            end) x
      end.

    Function simul (lbs : simul_state) {measure nb_next lbs} : @simul_result unit :=
      match nb_next lbs with
        | 0%nat => SimOk tt lbs
        | S n' =>
          match inM next lbs with
            | SimOk _ s' => simul (mk_simul_state (semst s') n')
            | SimKo s m => SimKo s m
          end
      end.
      unfold nb_next.
      auto with *.
    Defined.

  End Make.

End Make.