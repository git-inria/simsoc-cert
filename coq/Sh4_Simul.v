(**
SimSoC-Cert, a Coq library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the SH4 architecture following the:

SH-4, Software Manual, Renesas 32-Bit RISC, Rev.6.00 2006.09

Page numbers refer to Renesas_SH4_2006.pdf.

Instruction decoding and execution cycle.
*)

Set Implicit Arguments.

Require Import Bitvec Sh4 Sh4_Semantics Sh4_State Message.
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

Definition catch {A} (m : simul_semfun A) (f : _ -> simul_semfun A) : simul_semfun A :=
  fun lbs0 => 
  match m lbs0 with 
    | SimKo lbs m => f m lbs
    | x => x
  end.

Definition bind_s fs A (m : simul_semfun unit) (f : state -> simul_semfun A) : simul_semfun A :=
  fun lbs0 => 
  match m lbs0 with 
    | SimOk a lbs1 => f (fs lbs1) lbs1
    | SimKo s m => SimKo s m
  end.

Definition get_s0 {A} := @bind_s (fun x => s0 (semst x)) A (SimOk tt).
Definition get_st {A} := @bind_s (fun x => st (semst x)) A (SimOk tt).

Definition save_s0_true (lbs : simul_state) :=
  SimOk tt (mk_simul_state (let s := st (semst lbs) in mk_semstate nil true s s) (nb_next lbs)).

Module Make (Import I : INST).

  Definition handle_exception : simul_semfun unit :=
    fun lbs => 
      match handle_exception (semst lbs) with
      | Ok a lbs' => SimOk a (mk_simul_state lbs' (nb_next lbs))
      | Ko m | Todo m => SimKo lbs m
    end.

  Definition next : simul_semfun unit :=
    get_st (fun s lbs => match inst_set (cpsr s) with
      | None => SimKo lbs InvalidInstructionSet
      | Some SH4 =>
        let a := address_of_current_instruction s in
        let w := read s a Word in
          match decode w with
            | DecError m => SimKo lbs m
            | DecUnpredictable => SimKo lbs DecodingReturnsUnpredictable
            | DecUndefined_with_num fake => SimKo lbs ComplexSemantics (*handle_exception (add_exn s UndIns)*)
            | DecInst i =>
              match step i (semst lbs) with
                | Ok _ lbs' => handle_exception (mk_simul_state (mk_semstate (loc lbs') (bo lbs') (s0 lbs') (incr_PC_ARM (bo lbs') (st lbs'))) (nb_next lbs))
                | Ko m | Todo m => SimKo lbs m
              end
          end
    end).

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
