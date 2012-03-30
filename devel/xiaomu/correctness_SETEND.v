Require Import Globalenvs Memory.
Require Import Csyntax Csem Cstrategy Coqlib Integers Values Maps Errors. 
Require Import Arm6_State Arm6_Proc Arm6_SCC Bitvec Arm6.
Require Import setend_compcert.
Require Import projection.
Require Import my_inversion.
Require Import my_tactic.

Require Import Arm6_Simul.
Import I.
Import Arm6_Functions.Semantics.

Definition ebit_func_related (m:Mem.mem) (e:env) (ebit:bool):Prop:=
  bit_proj m e E = ebit.

Definition prog_setend := setend_compcert.p.

Definition set_bit_cpsr :=
  Ecall (Evalof (Evar set_bit T1) T1)
  (Econs
    (Ecall (Evalof (Evar StatusRegister_to_uint32 T2) T2)
      (Econs
        (Eaddrof
          (Efield (Ederef (Evalof (Evar proc T3) T3) T4)
            cpsr T5) T5) Enil) T6)
    (Econs (Eval (Vint (repr 9)) T7)
      (Econs (Evalof (Evar E T8) T8) Enil))) T9.

Lemma setbit_cpsr_ok :
  forall m e l b s t m' v ebit,
    proc_state_related m e (Ok tt (mk_semstate l b s))->
    eval_expression (Genv.globalenv prog_setend) e m set_bit_cpsr t m' v->
    proc_state_related m' e 
    (Ok tt (mk_semstate l b
    (Arm6_State.set_cpsr s (Bitvec.set_bit 9 ebit (Arm6_State.cpsr s))))).
Admitted.

Theorem correctness_SETEND : forall e m0 m1 m2 mfin vargs s out ebit,
  alloc_variables empty_env m0 
  (fun_internal_SETEND.(fn_params)++fun_internal_SETEND.(fn_vars)) e m1->
  bind_parameters e m1 fun_internal_SETEND.(fn_params) vargs m2->
  proc_state_related m2 e (Ok tt (mk_semstate nil true s)) ->
  ebit_func_related m2 e ebit ->
  exec_stmt (Genv.globalenv prog_setend) e m2 fun_internal_SETEND.(fn_body) 
  Events.E0 mfin out ->
  proc_state_related mfin e 
  (S.SETEND_step ebit (mk_semstate nil true s)).
Proof.
  intros until ebit. intros av bp psrel efrel exst.
  
  (* unfold setend body in C side *)
  inv exst. rename H2 into ee_call.
  
  apply setbit_cpsr_ok with m2 e nil true s Events.E0 mfin v ebit in psrel;
    [idtac|exact ee_call].

  (* unfold setend_step in Coq side *)
  unfold S.SETEND_step. unfold _get_st. unfold bind_s.
  unfold bind; simpl.
  exact psrel.
Qed.