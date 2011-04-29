(**
SimSoC-Cert, a toolkit for generating certified processor simulators
See the COPYRIGHTS and LICENSE files.

Proof of simlight.
*)

Set Implicit Arguments.

Require Import Csem Smallstep Events Integers Globalenvs AST Memory Csyntax
  Coqlib.
Import Genv.

Require Import Util Cnotations all.

Ltac norm e := let x := fresh in set (x := e); vm_compute in x; subst x.

Ltac norm_lhs := match goal with |- ?e = _ => norm e end.

Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro: forall b f m0,
      let ge := Genv.globalenv p in
      Genv.init_mem p = Some m0 ->
      Genv.find_symbol ge p.(prog_main) = Some b ->
      Genv.find_funct_ptr ge b = Some f ->
      type_of_fundef f = Tfunction T[int32; `*`(`*`int8)] (Tint I32 Signed) ->
      initial_state p (Callstate f nil Kstop m0).

Definition exec_program (p: program) (beh: program_behavior) : Prop :=
  program_behaves step (initial_state p) final_state (Genv.globalenv p) beh.

Open Scope positive_scope.

Set Printing Depth 10.

Lemma simlight_ok : exists t, exists k, exec_program p (Terminates t k).

Proof.
eapply ex_intro. eapply ex_intro. unfold exec_program.
set (ge := globalenv p). eapply program_terminates.
(* final state *)
3: apply final_state_intro.
(* initial state *)
eapply initial_state_intro.
2: norm_lhs; refl. 2: norm_lhs; refl. 2: refl.
(* steps *)
Focus 2.
eapply star_step. right. eapply step_internal_function.
list_norepet beq_positive_ok.
Ltac comp :=
  match goal with
    |- Csem.alloc_variables _ _ ?l _ _ => norm l
  end.
comp.
eapply alloc_variables_cons.