Require Import Globalenvs Memory.
Require Import Csyntax Csem Cstrategy Coqlib Integers Values Maps Errors. 
Require Import Arm6_State Arm6_Proc Arm6_SCC Bitvec Arm6.
Require Import ldrb_compcert.
Require Import projection.

Require Import Arm6_Simul.
Import I.
Import Arm6_Functions.Semantics.

Require Import my_inversion.
Require Import my_tactic.

Definition prog_ldrb := ldrb_compcert.p.

Definition ad_func_related (m:Mem.mem) (e:env) (addr:word):Prop:=
  bits_proj m e address = addr.

Definition cond_func_related (m:Mem.mem) (e:env) (cond:opcode):Prop:=
  cond_proj m e = cond.

Definition d_func_related (m:Mem.mem) (e:env) (d:regnum):Prop:=
  reg_proj m e ldrb_compcert.d = d.

Definition condpass :=
  Ecall (Evalof (Evar ConditionPassed T1) T1)
  (Econs
    (Eaddrof
      (Efield (Ederef (Evalof (Evar proc T2) T2) T3) cpsr T4)
      T5)
    (Econs (Evalof (Evar ldrb_compcert.cond T6) T6) Enil)) T7.

Lemma no_effect_condpass :
  forall e m t m' v,
    eval_expression (Genv.globalenv prog_ldrb) e m condpass t m' v->
    m = m'.
Admitted.

Lemma condpass_bool :
  forall m0 e m0' m t m' v cond s b,
    alloc_variables empty_env m0 
      (fun_internal_LDRB.(fn_params) ++ fun_internal_LDRB.(fn_vars)) e m0' ->
    eval_expression (Genv.globalenv prog_ldrb) e m condpass t m' v->
    bool_val v T7 = Some b->
    Arm6_Functions.State.ConditionPassed s cond = b.
Admitted.

Definition set_reg_pc_addr :=
  Ecall (Evalof (Evar set_reg_or_pc T8) T8)
  (Econs (Evalof (Evar proc T2) T2)
    (Econs (Evalof (Evar ldrb_compcert.d T9) T9)
      (Econs
        (Ecall (Evalof (Evar read_byte T10) T10)
          (Econs (Evalof (Evar address T11) T11) Enil) T9)
        Enil))) T12.

Lemma setregpc_addr_ok :
  forall m e l b s t m' v b' d addr,
    proc_state_related m e (Ok tt (mk_semstate l b s))->
    eval_expression (Genv.globalenv prog_ldrb) e m set_reg_pc_addr t m' v->
    proc_state_related m' e 
    (Ok tt (mk_semstate l b'
    (Arm6_State.set_reg s d 
      (Arm6_SCC.mem (scc s) (address_of_word addr))
      [first_bit addr + 7 # first_bit addr]))).
Admitted.

Theorem correctness_ldrb: forall e m0 m1 m2 mfin vargs s out addr cond d,
  alloc_variables empty_env m0 
  (fun_internal_LDRB.(fn_params) ++ fun_internal_LDRB.(fn_vars)) e m1 ->
  bind_parameters e m1 fun_internal_LDRB.(fn_params) vargs m2->
  proc_state_related m2 e (Ok tt (mk_semstate nil true s)) ->
  ad_func_related m2 e addr ->
  cond_func_related m2 e cond ->
  d_func_related m2 e d ->
  exec_stmt (Genv.globalenv prog_ldrb) e m2 fun_internal_LDRB.(fn_body) 
  Events.E0 mfin out ->
  proc_state_related mfin e (S.LDRB_step addr cond d (mk_semstate nil true s)).
Proof.
  intros until d. intros av bp psrel afrel cfrel dfrel exst.

  (* unfold LDRB body *)
  inv exst. rename H5 into ee_call, H8 into bvv1, H9 into exst, H4 into evnts.
  simpl in bvv1.

  (* m2 = m3 *)
  generalize ee_call; intro ee_call'.
  apply no_effect_condpass with e m2 t1 m3 v1 in ee_call'.
  rewrite<-ee_call' in *;clear ee_call' m3.
  
  (* Condition pass gives the same value in two sides *)
  generalize av; intro av'.
  apply condpass_bool with m0 e m1 m2 t1 m2 v1 cond s b in av';
    [idtac|exact ee_call|exact bvv1].
  clear ee_call.
  
  (* case on the boolean value of Condpass *)
  destruct b.

    (* condpass = true *)
    inv exst. rename H2 into ee_call.
    apply setregpc_addr_ok with m2 e nil true s t2 mfin v (Util.zne d 15) d 
      addr in psrel;[idtac|exact ee_call].

    (* unfold LDRB_step in Coq side *)
    unfold S.LDRB_step. unfold _get_st. unfold bind_s.
    unfold bind; simpl.
    rewrite av';simpl.
    unfold set_reg. unfold _Arm_State.set_reg.
    exact psrel.

    (* condpass = false *)
    inv exst.
    unfold S.LDRB_step. unfold _get_st. unfold bind_s.
    unfold bind; simpl.
    rewrite av';simpl.
    exact psrel.
Qed.
  
