Require Import Globalenvs Memory.
Require Import Csyntax Csem Cstrategy Coqlib Integers Values Maps Errors. 
Require Import Arm6_State Arm6_Proc Arm6_SCC Bitvec Arm6.
Require Import mrs_compcert.
Require Import projection.
Require Import my_inversion.
Require Import my_tactic.

Require Import Arm6_Simul.
Import I.
Import Arm6_Functions.Semantics.

Definition rbit_func_related (m:Mem.mem) (e:env) (rbit:bool):Prop:=
  bit_proj m e R = rbit.

Definition cond_func_related (m:Mem.mem) (e:env) (cond:opcode):Prop:=
  cond_proj m e = cond.

Definition d_func_related (m:Mem.mem) (e:env) (d:regnum):Prop:=
  reg_proj m e mrs_compcert.d = d.

Definition prog_mrs := mrs_compcert.p.

(* Return the memory model which only relates to this ident *)
Parameter of_mem : AST.ident -> Mem.mem -> Mem.mem.

Definition condpass :=
  Ecall (Evalof (Evar ConditionPassed T1) T1)
  (Econs
    (Eaddrof
      (Efield (Ederef (Evalof (Evar proc T2) T2) T3) cpsr T4)
      T5) (Econs (Evalof (Evar mrs_compcert.cond T6) T6) Enil)) T7.

Lemma no_effect_condpass :
  forall e m t m' v,
    eval_expression (Genv.globalenv prog_mrs) e m condpass t m' v->
    m = m'.
Admitted.

Lemma condpass_bool :
  forall m0 m0' e m t m' v cond s b,
    alloc_variables empty_env m0 
    (fun_internal_MRS.(fn_params) ++ fun_internal_MRS.(fn_vars)) e m0' ->
    eval_expression (Genv.globalenv prog_mrs) e m condpass t m' v ->
    bool_val v T7 = Some b ->
    Arm6_Functions.State.ConditionPassed s cond = b.
Admitted.

Definition is_R_set :=
  Ebinop Oeq (Evalof (Evar R T7) T7) 
  (Eval (Vint (repr 1)) T6) T6.

Lemma no_effect_is_R_set :
  forall e m t m' v,
    eval_expression (Genv.globalenv prog_mrs) e m is_R_set t m' v ->
    m = m'.
Proof.
  intros until v; intro ee_binop.
  inv ee_binop. rename H into ee_binop, H0 into esrv.
  unfold is_R_set in ee_binop.
  inv_binop m m'. intros until a2'. intros ee_valof ee_val esrv.
  inv_valof m m'0. intros until a'0. intros ee_var esrv.
  inv_var m m'0.
  inv_val m m'. intro esrv.
  reflexivity.
Qed.

Lemma R_bool :
  forall m0 e m0' m t m' v rbit b,
    alloc_variables empty_env m0 
      (fun_internal_MRS.(fn_params) ++ fun_internal_MRS.(fn_vars)) e m0' ->
    rbit_func_related m e rbit->
    eval_expression (Genv.globalenv prog_mrs) e m is_R_set t m' v ->
    bool_val v T7 = Some b->
    Util.zeq rbit 1 = b.
Proof.
  intros until b. intros av rfrel ee_R bvv.
  unfold rbit_func_related in rfrel. unfold bit_proj in rfrel.
  unfold param_val in rfrel.
  inv_alloc_vars e.
  pose (e:=
    PTree.set d (b3, Tint I8 Unsigned)
      (PTree.set cond (b2, Tint I32 Signed)
        (PTree.set R (b0, Tint I8 Signed)
          (PTree.set proc (b1, Tpointer typ_SLv6_Processor)
            empty_env)))).
  fold e in ee_R |-*;simpl.
  inv ee_R. rename H into ee_R, H0 into esrv.
  unfold is_R_set in ee_R.
  inv_binop m m'. intros until a2'. intros ee_valof ee_val esrv.
  inv_valof m m'0. intros until a'0. intros ee_var esrv.
  inv_var m m'0.
  inv_val m m'. intros esrv.
  inv esrv. rename H4 into esrv1, H5 into esrv2, H6 into sbo.
  inv esrv2.
  inv esrv1. rename H1 into esl, H4 into lvotv1. clear H2.
  simpl in sbo.
  inv esl;try discriminate. rename H3 into existR.
  simpl in existR;injection existR;clear existR;intros eq04;rewrite<-eq04 in *;
    clear b4 eq04.
  unfold T7 in lvotv1.
  rewrite lvotv1.
  unfold sem_cmp in sbo;simpl in sbo.
  destruct v1; try discriminate.
  injection sbo. clear sbo;intro eqv;rewrite<-eqv in *;clear eqv v.
  unfold varg_proj.
  unfold bool_val in bvv;simpl in bvv. unfold w1.
  unfold Val.of_bool in bvv;simpl in bvv.
  destruct (eq i (repr 1));simpl in bvv;injection bvv;intro eq;rewrite<-eq;simpl;
    reflexivity.
Qed.

Definition set_reg_pc_spsr :=
  Ecall (Evalof (Evar set_reg_or_pc T8) T8)
  (Econs (Evalof (Evar proc T2) T2)
    (Econs (Evalof (Evar mrs_compcert.d T9) T9)
      (Econs
        (Ecall
          (Evalof (Evar StatusRegister_to_uint32 T10) T10)
          (Econs
            (Ecall (Evalof (Evar spsr T11) T11)
              (Econs (Evalof (Evar proc T2) T2) Enil) T5)
            Enil) T12) Enil))) T13.

Definition set_reg_pc_cpsr :=
  Ecall (Evalof (Evar set_reg_or_pc T8) T8)
  (Econs (Evalof (Evar proc T2) T2)
    (Econs (Evalof (Evar mrs_compcert.d T9) T9)
      (Econs
        (Ecall
          (Evalof (Evar StatusRegister_to_uint32 T10) T10)
          (Econs
            (Eaddrof
              (Efield
                (Ederef (Evalof (Evar proc T2) T2) T3)
                cpsr T4) T4) Enil) T12) Enil))) T13.

Lemma setregpc_spsr_ok :
  forall m e l b s t m' v d,
    proc_state_related (of_mem proc m) e (Ok tt (mk_semstate l b s))->
    eval_expression (Genv.globalenv prog_mrs) e m set_reg_pc_spsr t m' v ->
    proc_state_related (of_mem proc m') e 
    (match Arm6_State.mode s with
       | usr =>
         unpredictable Arm6_Message.EmptyMessage
         {| loc := nil; bo := true; st := s |}
       | exn em =>
         set_reg d (Arm6_State.spsr s em)
         {| loc := nil; bo := true; st := s |}
       | sys =>
         unpredictable Arm6_Message.EmptyMessage
         {| loc := nil; bo := true; st := s |}
     end).
Admitted.

Lemma setregpc_cpsr_ok :
  forall m e l b s t m' v b' d,
    proc_state_related (of_mem proc m) e (Ok tt (mk_semstate l b s))->
    eval_expression (Genv.globalenv prog_mrs) e m set_reg_pc_cpsr t m' v ->
    proc_state_related (of_mem proc m') e
    (Ok tt (mk_semstate l b'
      (Arm6_State.set_reg s d (Arm6_State.cpsr s)))).
Admitted.

(*
Lemma R_not_change_setregpc :
  forall e m t m' a' R,
    rbit_func_related m e R ->
    eval_expr (Genv.globalenv prog_mrs) e m RV set_reg_pc_spsr t m' a'->
    rbit_func_related m' e R.
Admitted.

Lemma cond_not_change_setregpc :
  forall e m t m' a' cd,
    cond_func_related m e cd ->
    eval_expr (Genv.globalenv prog_mrs) e m RV set_reg_pc_spsr t m' a'->
    cond_func_related m' e cd.
Admitted.

Lemma d_not_changed_setregpc :
  forall e m t m' a' d,
    d_func_related m e d ->
    eval_expr (Genv.globalenv prog_mrs) e m RV set_reg_pc_spsr t m' a'->
    d_func_related m' e d.
Admitted.
*)

Theorem correctness_MSR : forall e m0 m1 m2 mfin vargs s out rbit cond d,
  alloc_variables empty_env m0 
  (fun_internal_MRS.(fn_params)++fun_internal_MRS.(fn_vars)) e m1->
  bind_parameters e m1 fun_internal_MRS.(fn_params) vargs m2->
  proc_state_related (of_mem proc m2) e (Ok tt (mk_semstate nil true s)) ->
  rbit_func_related m2 e rbit ->
  cond_func_related m2 e cond ->
  d_func_related m2 e d ->
  exec_stmt (Genv.globalenv prog_mrs) e m2 fun_internal_MRS.(fn_body) 
  Events.E0 mfin out ->
  proc_state_related (of_mem proc mfin) e 
  (S.MRS_step rbit cond d (mk_semstate nil true s)).
Proof.
  intros until d;intros av bp psrel rfrel cfrel dfrel exst.
  
  (* unfold MRS in C side *)
  inv exst. rename H5 into ee_cp, H8 into bvv1, H9 into exst, H4 into events.
  simpl in bvv1.
  generalize ee_cp; intro ee_cp'.

  (* m2 = m3 *)
  apply no_effect_condpass with e m2 t1 m3 v1 in ee_cp'.
  rewrite<-ee_cp' in *;clear m3 ee_cp'.

  (* condition pass gives the same result in two side *)
  generalize av; intro av'.
  apply condpass_bool with m0 m1 e m2 t1 m2 v1 cond s b in av';
    [idtac|exact ee_cp|exact bvv1].
  clear ee_cp.
  
  (* case on the boolean value of condpass *)
  destruct b.
   
    (* condpass = true *)
    inv exst. rename H4 into ee_binop, H8 into bvv0, H9 into exst.
    simpl in bvv0.

    (* m2 = m3 *)
    generalize ee_binop;intro ee_binop'.
    apply no_effect_is_R_set with e m2 t0 m3 v0 in ee_binop'.
    rewrite<-ee_binop' in *;clear m3 ee_binop'.
    
    (* R has the same value in two sides *)
    apply R_bool with m0 e m1 m2 t0 m2 v0 rbit b in av;
      [idtac|exact rfrel|exact ee_binop|exact bvv0].    
    
    (* case on R bit *)
    destruct b.

      (* R = 1 *)
      inv exst. rename H2 into ee_call.
      apply setregpc_spsr_ok with m2 e nil true s t3 mfin v d in psrel;
        [idtac|exact ee_call].
      
      (* unfold MRS in Coq side *)
      unfold S.MRS_step. unfold _get_st. unfold bind_s.
      unfold bind; simpl.
      rewrite av'; simpl.
      rewrite av; simpl.

      unfold if_CurrentModeHasSPSR;simpl.
      exact psrel.

      (* R = 0 *) 
      inv exst. rename H2 into ee_call.
      apply setregpc_cpsr_ok with m2 e nil true s t3 mfin v (Util.zne d 15) d
        in psrel; [idtac|exact ee_call].
      
      (* unfold MRS in Coq side *)
      unfold S.MRS_step. unfold _get_st. unfold bind_s.
      unfold bind;simpl.
      rewrite av';simpl.
      rewrite av;simpl.
      unfold set_reg. simpl. unfold _Arm_State.set_reg.
      exact psrel.

    (* if condition pass is false *)
    inv exst.
    
    (* unfold MRS in Coq side *)
    unfold S.MRS_step. unfold _get_st. unfold bind_s.
    unfold bind;simpl.
    rewrite av';simpl.
    exact psrel.
Qed.
