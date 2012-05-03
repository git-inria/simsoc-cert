Require Import Globalenvs Memory.
Require Import Csyntax Csem Cstrategy Coqlib Integers Values Maps Errors. 
Require Import Arm6_State Arm6_Proc Arm6_SCC Bitvec Arm6.
Require Import bl_compcert.
Require Import projection.

Require Import Arm6_Simul.
Import I.
Import Arm6_Functions.Semantics.

Require Import my_inversion.
Require Import my_tactic.
Require Import common_functions.

Set Implicit Arguments.

Definition fun_ConditionPassed :=
  common_functions.fun_ConditionPassed 
  bl_compcert.N_flag bl_compcert.Z_flag bl_compcert.C_flag bl_compcert.V_flag
  bl_compcert.Q_flag bl_compcert.J_flag 
  bl_compcert.GE0 bl_compcert.GE1 bl_compcert.GE2 bl_compcert.GE3 
  bl_compcert.E_flag bl_compcert.A_flag bl_compcert.I_flag bl_compcert.F_flag
  bl_compcert.T_flag 
  bl_compcert.mode bl_compcert.background bl_compcert.SLv6_StatusRegister
  bl_compcert.ConditionPassed.

Definition bl_functions :=
  fun_ConditionPassed :: bl_compcert.functions.

Definition prog_bl :=
  AST.mkprogram bl_functions bl_compcert.main bl_compcert.global_variables.

Definition lbit_func_related (m:Mem.mem) (e:env) (lbit:bool):Prop:=
  bit_proj m e L = lbit.

Definition cond_func_related (m:Mem.mem) (e:env) (cond:opcode):Prop:=
  cond_proj m e = cond.

Definition si24_func_related (m:Mem.mem) (e:env) (si24:word):Prop:=
  bits_proj m e signed_immed_24 = si24.

(* if the functions are not in the same generated file, they can't share same Lemma
   to prove, because the identifiers of a certain name are different. *)

Definition condpass :=
  Ecall (Evalof (Evar ConditionPassed T1) T1)
    (Econs
      (Eaddrof
        (Efield (Ederef (Evalof (Evar proc T2) T2) T3) cpsr T4) T5)
      (Econs (Evalof (Evar bl_compcert.cond T6) T6) Enil)) T7.

Lemma no_effect_condpass :
  forall e m m' t v,
    eval_expression (Genv.globalenv prog_bl) e m condpass t m' v ->    
    m = m'.
Admitted.

Lemma no_effect_condpass' :
  forall m0 e m0' m m' t v,
    alloc_variables empty_env m0 
      (fun_internal_B.(fn_params) ++ fun_internal_B.(fn_vars)) e m0' ->    
    eval_expression (Genv.globalenv prog_bl) e m condpass t m' v ->    
    m = m'.
Proof.
  intros until v;intros av ee.
  unfold condpass in ee.
  inv ee. rename H into ee, H0 into esrv.
  inv_eval_expr m m'.
  (* vres=v  *)
  inv esr0.
  (* vf is the value of ConditionPassed *)
  inv esr. rename H1 into esl,H4 into lvotvf. clear H2.
  (* e *)
  inv_alloc_vars e.
  pose (e:=PTree.set signed_immed_24 (b3, Tint I32 Unsigned)
               (PTree.set cond (b2, Tint I32 Signed)
                  (PTree.set L (b0, Tint I8 Signed)
                     (PTree.set proc (b1, Tpointer typ_SLv6_Processor)
                        empty_env)))).
  fold e in eslst, esl.

  inv esl.
  (* ConditionPassed is not in local env *)
  discriminate.
  (* ConditionPassed is in global env *)
  rename H1 into notine,H2 into fs,H5 into tog.

  find_func.
  eapply mem_not_changed_ef in ev_funcall.
  exact ev_funcall.
Qed.

Lemma condpass_bool :
  forall m0 e m0' m t m' v cond s b,
    alloc_variables empty_env m0 
      (fun_internal_B.(fn_params) ++ fun_internal_B.(fn_vars)) e m0' ->
    eval_expression (Genv.globalenv prog_bl) e m condpass t m' v ->
    bool_val v T7 = Some b ->
    Arm6_Functions.State.ConditionPassed s cond = b.
Proof.
Admitted.

Definition is_L_set :=
  (Ebinop Oeq (Evalof (Evar L T7) T7)
    (Eval (Vint (repr 1)) T6) T6).

Lemma no_effect_is_L_set :
  forall e m t m' v,
    eval_expression (Genv.globalenv prog_bl) e m is_L_set t m' v->
    m = m'.
Proof.
  intros until v; intro ee_L.
  inv ee_L. rename H into ee_L, H0 into esrv.
  unfold is_L_set in ee_L.
  inv_binop m m'. intros until a2'; intros ee_valof ee_val esrv.
  inv_valof m m'0. intros until a'0; intros ee_var esrv.
  inv_var m m'0. inv_val m m'. intro. reflexivity.
Qed.

Lemma L_bool :
  forall m0 e m0' m t m' v lbit b,
    alloc_variables empty_env m0 
      (fun_internal_B.(fn_params) ++ fun_internal_B.(fn_vars)) e m0' ->
    lbit_func_related m e lbit ->
    eval_expression (Genv.globalenv prog_bl) e m is_L_set t m' v ->
    bool_val v T7 = Some b->
    Util.zeq lbit 1 = b.
Proof.
  intros until b; intros av lfr ee_L bv .
  inv_alloc_vars e.
  unfold lbit_func_related in lfr. unfold bit_proj in lfr.
  unfold param_val in lfr.
  unfold varg_proj in lfr.
  pose (e:=
    (PTree.set signed_immed_24 (b3, Tint I32 Unsigned)
      (PTree.set cond (b2, Tint I32 Signed)
        (PTree.set L (b0, Tint I8 Signed)
          (PTree.set proc (b1, Tpointer bl_compcert.typ_SLv6_Processor)
            empty_env)))));
  fold e in ee_L, lfr;simpl in lfr.

  inv ee_L. rename H into ee_L, H0 into esrv.
  unfold is_L_set in ee_L.
  inv_binop m m'. intros until a2'; intros ee_valof ee_val esrv .
  inv_valof m m'0. intros until a'0; intros ee_L esrv.
  inv_var m m'0.
  inv_val m m'. intro esrv.

  inv esrv. rename H4 into esrv1, H5 into esrv2, H6 into sbo.
  inv esrv1. rename H1 into esl, H4 into ld_v1. clear H2.
  inv esl;
  [rename H3 into existl;simpl in existl;injection existl;clear existl;intro eq40;
    rewrite<-eq40 in *;clear eq40 b4
    |rename H1 into existl;simpl in existl;discriminate].

  fold T7. rewrite ld_v1.
  inv esrv2.
  simpl in sbo.
  
  unfold sem_cmp in sbo. simpl in sbo.
  destruct v1; try discriminate.
  injection sbo;clear sbo;intro eqiv;rewrite<-eqiv in *;clear eqiv v.

  (* case on the boolean value of b *)
  destruct b;
    unfold bool_val in bv; simpl in bv;
      unfold Val.of_bool in bv; simpl in bv;
        unfold w1.
    (* true *)
    destruct (eq i (repr 1));simpl;
      [reflexivity|simpl in bv;discriminate].
    (* false *)
    destruct (eq i (repr 1));simpl;
      [simpl in bv;discriminate|reflexivity].
Qed.

Definition set_reg_aoni:=
  Ecall (Evalof (Evar bl_compcert.set_reg T8) T8)
  (Econs (Evalof (Evar proc T2) T2)
    (Econs (Eval (Vint (repr 14)) T6)
      (Econs
        (Ecall
          (Evalof (Evar address_of_next_instruction T9)
            T9)
          (Econs (Evalof (Evar proc T2) T2) Enil) T10)
        Enil))) T11.
  

Lemma set_reg_aoni_ok :
  forall e m t m' a' l b s, 
    proc_state_related m e (Ok tt (mk_semstate l b s)) ->
    eval_expr (Genv.globalenv prog_bl) e m RV set_reg_aoni t m' a'->
    (forall l b,proc_state_related m' e
      (Ok tt (mk_semstate l b 
        (Arm6_State.set_reg s LR (Arm6_State.address_of_next_instruction s))))).
Admitted.

Definition set_pc_rw_x :=
  Ecall (Evalof (Evar set_pc_raw T12) T12)
  (Econs (Evalof (Evar proc T2) T2)
    (Econs
      (Ebinop Oadd
        (Ecall (Evalof (Evar reg T13) T13)
          (Econs (Evalof (Evar proc T2) T2)
            (Econs (Eval (Vint (repr 15)) T6) Enil))
          T10)
        (Ebinop Oshl
          (Ecall
            (Evalof (Evar SignExtend_30 T14) T14)
            (Econs
              (Evalof (Evar signed_immed_24 T10)
                T10) Enil) T10)
          (Eval (Vint (repr 2)) T6) T10) T10) Enil)) T11.

Lemma set_pc_rw_x_ok :
  forall e m t m' a' l b s si24,
    proc_state_related m e (Ok tt (mk_semstate l b s)) ->
    si24_func_related m e si24 ->
    eval_expr (Genv.globalenv prog_bl) e m RV set_pc_rw_x t m' a' ->
    proc_state_related m' e 
    (Ok tt 
      (mk_semstate l false
      (Arm6_State.set_reg s PC (add (Arm6_State.reg_content s PC) 
        (Arm6_Functions.Logical_Shift_Left 
          (Arm6_Functions.SignExtend_30 si24) (repr 2)))))).
Admitted.

Lemma L_not_change_set_reg_aoni :
  forall e m t m' a' L,
    lbit_func_related m e L ->
    eval_expr (Genv.globalenv prog_bl) e m RV set_reg_aoni t m' a'->
    lbit_func_related m' e L.
Admitted.

Lemma cond_not_change_set_reg_aoni :
  forall e m t m' a' cd,
    cond_func_related m e cd ->
    eval_expr (Genv.globalenv prog_bl) e m RV set_reg_aoni t m' a'->
    cond_func_related m' e cd.
Admitted.

Lemma si24_not_change_set_reg_aoni :
  forall e m t m' a' si24,
    si24_func_related m e si24 ->
    eval_expr (Genv.globalenv prog_bl) e m RV set_reg_aoni t m' a'->
    si24_func_related m' e si24.
Admitted.

Lemma L_not_change_set_pc_rw :
  forall e m t m' a' L,
    lbit_func_related m e L ->
    eval_expr (Genv.globalenv prog_bl) e m RV set_pc_rw_x t m' a'->
    lbit_func_related m' e L.
Admitted.

Lemma cond_not_change_set_pc_rw :
  forall e m t m' a' cd,
    cond_func_related m e cd ->
    eval_expr (Genv.globalenv prog_bl) e m RV set_pc_rw_x t m' a'->
    cond_func_related m' e cd.
Admitted.

Lemma si24_not_change_set_pc_rw :
  forall e m t m' a' si24,
    si24_func_related m e si24 ->
    eval_expr (Genv.globalenv prog_bl) e m RV set_pc_rw_x t m' a'->
    si24_func_related m' e si24.
Admitted.

Theorem correctness_BL: forall e m0 m1 m2 mfin vargs s out L cond si24,
  alloc_variables empty_env m0 
  (fun_internal_B.(fn_params) ++ fun_internal_B.(fn_vars)) e m1 ->
  bind_parameters e m1 fun_internal_B.(fn_params) vargs m2 ->
(* TODO: valid_access needs to be more precise *)
  (forall m ch b ofs, Mem.valid_access m ch b ofs Readable) ->
  proc_state_related m2 e (Ok tt (mk_semstate nil true s)) ->
  lbit_func_related m2 e L ->
  cond_func_related m2 e cond ->
  si24_func_related m2 e si24 ->
  exec_stmt (Genv.globalenv prog_bl) e m2 fun_internal_B.(fn_body) 
  Events.E0 mfin out ->
  proc_state_related mfin e 
  (S.B_step L cond si24 (mk_semstate nil true s)).
Proof.

  intros until si24. intros av bp memvld psrel lfrel cfrel sfrel exst.
  
  (* expand exec_stmt , between m2 mfin *)
  inv exst. 
  
  rename H5 into cp, H8 into cp_bool, H9 into exst, H4 into trc.
  simpl in cp_bool.

  (* evalutate e *)
  (*
  inv_alloc_vars e.
  pose (e:=(PTree.set signed_immed_24 (b3, Tint I32 Unsigned)
        (PTree.set bl_compcert.cond (b2, Tint I32 Signed)
           (PTree.set bl_compcert.L (b0, Tint I8 Signed)
              (PTree.set proc (b1, Tpointer typ_SLv6_Processor) empty_env)))));
  fold e in bp,psrel,lfrel,cfrel,sfrel,cp,exst|-*.
  *)
  (* condpass doesn't change mem, m2 = m3 *)
  generalize cp; intro cp'.

  eapply no_effect_condpass in cp.
  rewrite cp in *. clear cp m2.

  (* condpass has the same value in both side *)
  generalize av;intros av'.
  apply condpass_bool with m0 e m1 m3 t1 m3 v1 cond s b in av';
    [idtac|exact cp'|exact cp_bool].

  (* case on the boolean value of condpass *)
  destruct b.
  (* if condpass = true *)
    inv exst; rename H3 into es_seq1, H7 into es_seq2;
    (* outcome is normal *)
    [idtac|
    (* outcome is not normal *)
    inv es_seq1;
    rename H4 into ee_l, H8 into bv_l, H9 into es_set_reg;
    (* case on the boolean value of L *)
    (* outcome of Sdo and Sskip is normal *)
    destruct b; inv es_set_reg; tauto].

    (* continue the case of outcome is normal *)
    (* first seq: if L then set R14 with address_of_next_instr *)
    inv es_seq1.
    rename H4 into ee_l, H8 into bv0, H9 into es_set_reg.
    generalize ee_l;intro ee_l'.
    (* m3 = m4 *)
    inv ee_l. rename H into ee_l, H0 into esrv0.
    inv_binop m3 m4.
    intros until a2'. intros ee_evalof ee_eval esrv0.
    inv_valof m3 m'. intros until a'0. intros ee_var esrv0.
    inv_var m3 m'.
    inv_val m3 m4. intros.

    (* (L==1) has the same value in both side *)
    generalize av;intro booll.
    apply L_bool with m0 e m1 m3 t2 m3 v0 L b in booll;
    [idtac|exact lfrel|fold is_L_set in ee_l';exact ee_l'|exact bv0].

    (* case on the boolean value of L *)

    destruct b.

      (* if L = 1 *)
      inv es_set_reg. rename H2 into ee_set_reg.
      inv ee_set_reg. rename H into ee_set_reg, H0 into esr.

      (* relation between m3 and m2 of funcall set_reg *)
      (*inv_call m3 m2. intros until vres.
      intros ee_val eelst esrvf eslst _ ff _ ev_func esrv.
      
      (* m3= m5 *)
      inv_valof m3 m5. intros until a'2. intros ee_var esrvf.
      inv_var m3 m5.
      *)
      apply set_reg_aoni_ok with e m3 t4 m2 a'1 nil true s nil true in psrel;
        [idtac|exact ee_set_reg].

      apply L_not_change_set_reg_aoni with e m3 t4 m2 a'1 L in lfrel;
        [idtac|exact ee_set_reg].

      apply cond_not_change_set_reg_aoni with e m3 t4 m2 a'1 cond in cfrel;
        [idtac|exact ee_set_reg].

      apply si24_not_change_set_reg_aoni with e m3 t4 m2 a'1 si24 in sfrel;
        [idtac|exact ee_set_reg].

      clear ee_set_reg. simpl in bv0.
      
      (* second seq *)
      inv es_seq2. rename H2 into ee_set_pc_rw.
      inv ee_set_pc_rw. rename H into ee_set_pc_rw, H0 into esrv2.
      apply set_pc_rw_x_ok with e m2 t3 mfin a'2 nil true 
        (Arm6_State.set_reg s LR (Arm6_State.address_of_next_instruction s)) si24
        in psrel;
        [idtac| exact sfrel| exact ee_set_pc_rw].
      
      apply L_not_change_set_pc_rw with e m2 t3 mfin a'2 L in lfrel;
        [idtac|exact ee_set_pc_rw].

      apply cond_not_change_set_pc_rw with e m2 t3 mfin a'2 cond in cfrel;
        [idtac|exact ee_set_pc_rw].

      apply si24_not_change_set_pc_rw with e m2 t3 mfin a'2 si24 in sfrel;
        [idtac|exact ee_set_pc_rw].

      (* unfold Coq side B_step *)
      unfold S.B_step. unfold _get_st. unfold bind_s.
      unfold bind;simpl.
      rewrite av';simpl.
      rewrite booll;simpl.
      unfold block. unfold fold_left. unfold _get_bo. unfold bind_s. unfold next.
      unfold bind. simpl. unfold _Arm_State.set_reg.
      exact psrel.

      (* if L<>1 *)
      
      (* first seq is Sskip *)
      inv es_set_reg. 
      (* second seq *)
      inv es_seq2. rename H2 into ee_set_pc_raw.
      inv ee_set_pc_raw. rename H into ee_set_pc_raw, H0 into esrv.
      apply set_pc_rw_x_ok with e m2 t3 mfin a'1 nil true s si24 in psrel;
        [idtac|exact sfrel|exact ee_set_pc_raw].

      apply L_not_change_set_pc_rw with e m2 t3 mfin a'1 L in lfrel;
        [idtac|exact ee_set_pc_raw].

      apply cond_not_change_set_pc_rw with e m2 t3 mfin a'1 cond in cfrel;
        [idtac|exact ee_set_pc_raw].

      apply si24_not_change_set_pc_rw with e m2 t3 mfin a'1 si24 in sfrel;
        [idtac|exact ee_set_pc_raw].

      (* unfold Coq side B_step *)
      unfold S.B_step. unfold _get_st. unfold bind_s.
      unfold bind;simpl.
      rewrite av';simpl.
      rewrite booll;simpl.
      unfold block. unfold fold_left. unfold _get_bo. unfold bind_s. unfold next.
      unfold bind. simpl. unfold _Arm_State.set_reg.
      exact psrel.

    (* if condpass = false *)
    inv exst.
    unfold S.B_step. unfold _get_st. unfold bind_s.
    unfold bind;simpl.
    rewrite av';simpl.
    exact psrel.
Qed.