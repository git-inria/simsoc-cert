(**
SimSoC-Cert, a toolkit for generating certified processor simulators
See the COPYRIGHTS and LICENSE files.

Proof of simlight.
*)

Set Implicit Arguments.

Require Import Csem Smallstep Events Integers Globalenvs AST Memory Csyntax
  Coqlib.
Import Genv.

Require Import Util Cnotations add.

Ltac norm e := let x := fresh in set (x := e); vm_compute in x; subst x.

Ltac comp :=
  match goal with
    | |- ?l = _ => norm l
    | |- Csem.alloc_variables _ _ ?l _ _ => norm l
    | |- Csem.bind_parameters _ _ ?l _ _ => norm l
  end.

Ltac alloc :=
  match goal with
    | |- Csem.alloc_variables _ _ nil _ _ => apply alloc_variables_nil
    | |- Csem.alloc_variables _ _ (cons _ _) _ _ =>
      eapply alloc_variables_cons; [comp; refl | alloc]
  end.

Ltac bind :=
  match goal with
    | |- Csem.bind_parameters _ _ nil _ _ => apply bind_parameters_nil
    | |- Csem.bind_parameters _ _ (cons _ _) _ _ =>
      eapply bind_parameters_cons; [comp; refl | bind]
  end.

Open Scope positive_scope.

Set Printing Depth 10.

Lemma add_ok : exists t, exists k, exec_program p (Terminates t k).

Proof.
eapply ex_intro. eapply ex_intro. unfold exec_program.
set (ge := globalenv p). eapply program_terminates.
(* final state *)
3: apply final_state_intro.
(* initial state *)
eapply initial_state_intro.
comp; refl.
comp; refl.
comp; refl.
refl.
(* steps *)
eapply star_step.
right. eapply step_internal_function.
list_norepet beq_positive_ok.
comp. alloc.
comp. bind.
eapply star_step. simpl fn_body.
right. eapply step_seq.
eapply star_step.
right. eapply step_do_1.
eapply star_step.
left. eapply step_lred with (C:=fun x => x `= _ `: _).
eapply red_var_local. comp; refl.
unfold not_stuck. intros.

eapply step_rred with (C:=fun x => x).
eapply red_assign.
eapply red_var_local.