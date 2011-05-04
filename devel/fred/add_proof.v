(**
SimSoC-Cert, a toolkit for generating certified processor simulators
See the COPYRIGHTS and LICENSE files.

Proof of simlight.
*)

Set Implicit Arguments.

Require Import Csem Cstrategy Smallstep Events Integers Globalenvs AST Memory
  Csyntax Coqlib.
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

Set Printing Depth 11.

Ltac s := eapply star_step; [right|idtac|idtac].
Ltac e := eapply star_step; [left |idtac|idtac].

Lemma add_ok : exists t, exists k, exec_program p (Terminates t k).

Proof.
eapply ex_intro. eapply ex_intro.
unfold exec_program. set (ge := globalenv p).
eapply program_terminates.

(* final state *)
3: apply final_state_intro.

(* initial state *)
eapply initial_state_intro.
comp; refl.
comp; refl.
comp; refl.
refl.

(* steps *)
s. eapply step_internal_function.
list_norepet beq_positive_ok.
comp; alloc.
comp; bind.

(* x = 2 *)
s. apply step_seq.
s. apply step_do_1.

e. eapply step_assign with (C:=fun x =>x).
apply lctx_top.
apply esl_var_local. comp; refl.
apply esr_val.
simpl typeof. apply cast_nn_i; apply nfc_int.
comp; refl.
refl.

s. apply step_do_2.
s. apply step_skip_seq.

(* y = 3 *)
s. apply step_seq.
s. apply step_do_1.

e. eapply step_assign with (C:=fun x =>x).
apply lctx_top.
apply esl_var_local. comp; refl.
apply esr_val.
simpl typeof. apply cast_nn_i; apply nfc_int.
comp; refl.
refl.

s. apply step_do_2.
s. apply step_skip_seq.

(* return x + y *)
s. apply step_return_1.
e. apply step_expr.
eapply esr_binop.
eapply esr_rvalof.
apply esl_var_local. comp; refl.
refl.
comp. refl.
eapply esr_rvalof.
apply esl_var_local. comp; refl.
refl.
comp; refl.
