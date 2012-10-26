Require Import Globalenvs Memory.
Require Import Csyntax Csem Cstrategy Coqlib Integers Values Maps Errors. 
Require Import Arm6_State Arm6_Proc Arm6_SCC Bitvec Arm6.
Require Import adc_compcert.
Require Import projection.
Require Import my_inversion.
Require Import my_tactic.
Require Import common_functions.

Require Import Arm6_Simul.
Import I.
Import Arm6_Functions.Semantics.

(* Add function CondictionPassed into global environment. *)
Definition fun_ConditionPassed :=
  common_functions.fun_ConditionPassed adc_compcert.ConditionPassed.

Definition adc_functions :=
  fun_ConditionPassed :: adc_compcert.functions.

(* Re-new the program of BL *)
Definition prog_adc :=
  AST.mkprogram adc_functions adc_compcert.main adc_compcert.global_variables.

(* Functional relation between the C memory module which contains the other ADC parameters, 
   and the COQ specification of ADC parameters *)
Definition sbit_func_related (m:Mem.mem) (e:env) (sbit:bool):Prop:=
  bit_proj m e S = sbit.

Definition cond_func_related (m:Mem.mem) (e:env) (cond:opcode):Prop:=
  cond_proj adc_compcert.cond m e = cond.

Definition d_func_related (m:Mem.mem) (e:env) (d:regnum):Prop:=
  reg_proj m e adc_compcert.d = d.

Definition n_func_related (m:Mem.mem) (e:env) (n:regnum):Prop:=
  reg_proj m e adc_compcert.n = n.

Definition so_func_related (m:Mem.mem) (e:env) (so:word):Prop:=
  bits_proj m e shifter_operand = so.

(*Print fun_internal_ADC.*)

Definition reg_id id :=
  Ecall (Evalof (Evar reg T2) T2)
  (Econs (Evalof (Evar adc_compcert.proc T3) T3)
    (Econs 
      (Evalof (Evar id T4) T4) Enil)) T1.

Definition get_rd_bit31 :=
  Ecall (Evalof (Evar get_bit T17) T17)
  (Econs (reg_id d)
    (Econs (Eval (Vint (repr 31)) T9)
      Enil)) T10.

(* Assume that every function that ADC calls, executes correctly
   and the C proc and ARM state related after these function execution *)

Lemma functions_behavior_ok:
  forall e l b s vf fd m vargs t m' vres l' b' s',
    proc_state_related proc m e (Ok tt (mk_semstate l b s)) ->
    Genv.find_funct (Genv.globalenv prog_adc) vf = Some fd ->
    eval_funcall (Genv.globalenv prog_adc) m fd vargs t m' vres ->
    proc_state_related proc m' e (Ok tt (mk_semstate l' b' s')).
Proof.
Admitted.

(* Assume that call to unpredictable leads to an Ko result*)
Lemma funct_unpredictable:
  forall e semstt vf fd m vargs t m' vres,
    proc_state_related proc m e (Ok tt semstt) ->
    Genv.find_funct (Genv.globalenv prog_adc) vf = Some fd ->
    eval_funcall (Genv.globalenv prog_adc) m fd vargs t m' vres ->
    proc_state_related proc m' e 
    (unpredictable Arm6_Message.EmptyMessage semstt).
Proof.
Admitted.

(* Assume function reg_n only load from memory, not change it*)
Lemma get_reg_ok :
  forall e id m t m' r,
    eval_expr (Genv.globalenv prog_adc) e m RV (reg_id id) t m' r ->
    eval_expr (Genv.globalenv prog_adc) e m RV (reg_id id) t m r/\m=m'.
Proof.
Admitted.

Definition oldrn_assgnt := 
  Eassign (Evar old_Rn T1) (reg_id n) T1.

(* Assum the assignment of old_Rn has no effect on the part of memory
   where located proc*)

Lemma oldrn_assgnt_ok':
 forall e m l b s t m' v,
  proc_state_related proc m e (Ok tt (mk_semstate l b s)) ->
  forall b_reg, e!reg = Some(b_reg,T2) ->
  eval_expression (Genv.globalenv prog_adc) e m
    oldrn_assgnt t m' v ->
  proc_state_related proc m' e (Ok tt (mk_semstate l b s)).
Proof.
  intros until v. intros psrel b_reg exist_reg rn_as.
  inv rn_as. rename H into ee, H0 into esrv.
  unfold oldrn_assgnt in ee.
  unfold reg_id in ee.
  inv_eval_expr m m'.
  inv esr0. rename H1 into esl0,H4 into lvot_vf;clear H2.
  inv esl0;[idtac|rewrite exist_reg in H1;discriminate].
  rename H3 into e_reg. rewrite exist_reg in e_reg.

  (*HERE*)
Admitted.

Lemma set_oldrn_ok:
  forall m m' v oldrn_blk ofs,
    store_value_of_type T1 m oldrn_blk ofs v = Some m' ->
     m = m'.
Proof.
Admitted.

Lemma oldrn_assgnt_ok:
 forall e m l b s t m' v,
  proc_state_related proc m e (Ok tt (mk_semstate l b s)) ->
  eval_expression (Genv.globalenv prog_adc) e m
    oldrn_assgnt t m' v ->
  proc_state_related proc m' e (Ok tt (mk_semstate l b s)).
Proof.
  intros until v. intros psrel rn_as.
  
  inv rn_as. rename H into ee, H0 into esrv.
  unfold oldrn_assgnt in ee.
  inv_eval_expr m m'.
  eapply get_reg_ok in ev_ex1. inv ev_ex1.
  simpl in *.
  eapply set_oldrn_ok in svot.
  
  rewrite <- svot. exact psrel.
Qed.

(* Lemmas on if ConditionPassed*)
Definition condpass :=
  Ecall (Evalof (Evar ConditionPassed T5) T5)
  (Econs
    (Eaddrof
      (Efield (Ederef (Evalof (Evar adc_compcert.proc T3) T3) T6) cpsr
        T7) T8) (Econs (Evalof (Evar adc_compcert.cond T9) T9) Enil))
  T10.

Lemma no_effect_condpass :
  forall e m m' t v,
    e! ConditionPassed = None ->
    eval_expression (Genv.globalenv prog_adc) e m condpass t m' v ->
    m = m'.
Proof.
  intros until v. intros noexists ee.
  inv ee. rename H into ee, H0 into esr.
  unfold condpass in ee.
  (* mem state between m and m' *)
  inv_eval_expr m m'.
  (* v = Eval vres T10 *)
  inv esr1.
  (* vf = the value of conditionPassed *)  
  inv esr0. rename H1 into esl, H4 into lvot. clear H2.

  inv esl; rewrite noexists in *. try discriminate.
  rename H2 into find_symbol, H5 into tog. clear H1.

  find_func.
  eapply mem_not_changed_ef in ev_funcall.
  exact ev_funcall.
Qed.

Lemma condpass_bool :
  forall m0 m0' e m l b s cond t m' v bv,
    alloc_variables empty_env m0 
      (fun_internal_ADC.(fn_params) ++ fun_internal_ADC.(fn_vars)) e m0' ->
    proc_state_related proc m e (Ok tt (mk_semstate l b s)) ->
    cond_func_related m e cond ->
    eval_expression (Genv.globalenv prog_adc) e m condpass t m' v ->
    bool_val v T4 = Some bv ->
    Arm6_Functions.State.ConditionPassed s cond = bv.
Proof.
Admitted.


(*Lemma on proc_state_relates holds after set_reg*)
Definition set_regpc :=
  Ecall (Evalof (Evar set_reg_or_pc T11) T11)
  (Econs (Evalof (Evar adc_compcert.proc T3) T3)
    (Econs (Evalof (Evar d T4) T4)
      (Econs
        (Ebinop Oadd
          (Ebinop Oadd
            (Evalof (Evar old_Rn T1) T1)
            (Evalof (Evar shifter_operand T1) T1)
            T1)
          (Evalof
            (Efield
              (Efield
                (Ederef
                  (Evalof (Evar adc_compcert.proc T3) T3)
                  T6) cpsr T7) C_flag T10) T10)
          T10) Enil))) T12.

Definition add_old_Rn_so_Cf :=
  Ebinop Oadd
  (Ebinop Oadd
    (Evalof (Evar old_Rn T1) T1)
    (Evalof (Evar shifter_operand T1) T1)
    T1)
  (Evalof
    (Efield
      (Efield
        (Ederef
          (Evalof (Evar adc_compcert.proc T3) T3)
          T6) cpsr T7) C_flag T10) T10) T10.

Lemma same_result_add_old_Rn_so_Cf :
  forall ge e m v s0 n so s,
    proc_state_related proc m e (Ok tt (mk_semstate nil true s)) ->
    n_func_related m e n ->
    so_func_related m e so ->
    eval_simple_rvalue ge e m add_old_Rn_so_Cf (Vint v) ->
    v = add (add (Arm6_State.reg_content s0 n) so)
    ((Arm6_State.cpsr s)[Cbit]).
Proof.
Admitted.


Lemma same_setregpc :
  forall e m l b s0 s t m' v d n so ,
    proc_state_related proc m e (Ok tt (mk_semstate l b s)) ->
    eval_expression (Genv.globalenv prog_adc) e m set_regpc t m' v ->
    (forall l b, proc_state_related proc m' e 
      (Ok tt (mk_semstate l b
        (Arm6_State.set_reg s d (add (add (Arm6_State.reg_content s0 n) so)
          ((Arm6_State.cpsr s)[Cbit]) ))))).
Proof.
Admitted.


(* Lemmas on if S==1 *)

Definition is_S_set :=
  Ebinop Oeq (Evalof (Evar S T10) T10)
    (Eval (Vint (repr 1)) T9) T9.

Lemma no_effect_is_S_set :
  forall e m t m' v,
    eval_expression (Genv.globalenv prog_adc) e m is_S_set t m' v ->
    m = m'.
Proof.
  intros until v. intros is_s. 
  inv is_s. unfold is_S_set in H.  
  inv_eval_expr m m'.
  reflexivity.
Qed.

Lemma S_bool :
  forall m0 e m0' m t m' v sbit b,
    alloc_variables empty_env m0 
      (fun_internal_ADC.(fn_params) ++ fun_internal_ADC.(fn_vars)) e m0' ->
    sbit_func_related m e sbit ->
    eval_expression (Genv.globalenv prog_adc) e m is_S_set t m' v ->
    bool_val v T9 = Some b->
    Util.zeq sbit 1 = b.
Proof.
  intros until b. intros av sfrel ee bv.
  unfold sbit_func_related in sfrel. unfold bit_proj in sfrel.
  unfold param_val in sfrel.
  inv_alloc_vars av e.
  pose (e:=
    (PTree.set old_Rn (b6, Tint I32 Unsigned)
      (PTree.set shifter_operand (b5, Tint I32 Unsigned)
        (PTree.set n (b4, Tint I8 Unsigned)
          (PTree.set d (b3, Tint I8 Unsigned)
            (PTree.set adc_compcert.cond (b2, Tint I32 Signed)
              (PTree.set S (b0, Tint I8 Signed)
                (PTree.set adc_compcert.proc (b1, Tpointer typ_SLv6_Processor)
                  empty_env))))))));
  fold e in ee;simpl.
  (* Find the relation between memory states m and m' *)
  inv ee. rename H into ee, H0 into esr. 
  unfold is_S_set in ee.
  (* Find the relation between memory states m and m' *)
  inversion ee. subst; clear ee.
  inversion H8. subst; clear H8.
  inversion H3. subst; clear H3.
  inversion H9. subst; clear H9.



  inv_eval_expr m m'.
  (* params of binop eq *)
  (* esr_binop in m' *)
  inv esr. simpl in H6.
  (* S *)
  (* esr_valof in m' *)
  inv H4. clear H2.
  (* esl_var_local in m' *)
  inv H1;[simpl in H4;injection H4;intro Heq;rewrite<-Heq in *;clear b7 Heq H4
    |discriminate].
  (* v6 is the value of S in m' *)
  unfold T10 in H7;simpl in H7;rewrite H7.
  (* esr_rval in m' *)
  inv H5.
  (* v1 is either Vint of Vptr *)
  destruct v1;
    [discriminate
      |unfold sem_cmp in H6;simpl in H6;
        injection H6;intro Heq;rewrite<-Heq in *;clear Heq H6 v
      |discriminate
      |discriminate].
  unfold varg_proj.
  unfold bool_val in bv;simpl in bv.
  unfold w1.
  destruct (eq i (repr 1));
  simpl in bv;injection bv;intro;rewrite<-H;clear H bv b;
  reflexivity.
Qed.

(* Lemmas on if (((S == 1) && (d == 15)))*)
Definition is_S_set_and_is_pc :=
  Econdition
  (Ebinop Oeq (Evalof (Evar S T10) T10)
    (Eval (Vint (repr 1)) T9) T9)
  (Econdition
    (Ebinop Oeq (Evalof (Evar d T4) T4)
      (Eval (Vint (repr 15)) T9) T9)
    (Eval (Vint (repr 1)) T9)
    (Eval (Vint (repr 0)) T9) T9)
  (Eval (Vint (repr 0)) T9) T9.


Lemma no_effect_is_S_set_and_is_pc :
  forall e m t m' v,
    eval_expression (Genv.globalenv prog_adc) e m is_S_set_and_is_pc t m' v ->
    m = m'.
Proof.
  intros until v. intro ee.
  inv ee.
  unfold is_S_set_and_is_pc in H.
  inv_eval_expr m m'.
  destruct b.
    (*b1 true*)
    inv_eval_expr m'0 m'.
    destruct b.
      (*b2 true*)
      inv_eval_expr m'1 m'.
      reflexivity.
      (*b2 false*)
      inv_eval_expr m'1 m'.
      reflexivity.
    (*b1 false*)
    inv_eval_expr m'0 m'.
    reflexivity.
Qed.

Lemma S_pc_bool :
  forall e m t m' v sbit d b,
    sbit_func_related m e sbit ->
    d_func_related m e d ->
    eval_expression (Genv.globalenv prog_adc) e m is_S_set_and_is_pc t m' v ->
    bool_val v T9 = Some b ->
    Util.zeq sbit 1 && Util.zeq d 15 = b.
Proof.
Admitted.

(* Lemmas on if CurrentModeHasSPSR *)
Definition hasSPSR :=
  Ecall (Evalof (Evar CurrentModeHasSPSR T13) T13)
  (Econs (Evalof (Evar adc_compcert.proc T3) T3) Enil) T10.

Lemma if_hasSPSR_ok :
  forall e m t m' v,
    eval_expression (Genv.globalenv prog_adc) e m hasSPSR t m' v ->
    m = m'.
Proof.
Admitted.

Lemma hasSPSR_true :
  forall m0 m0' m0'' e m vargs t m' v l b s em,
    alloc_variables empty_env m0 
      (fun_internal_ADC.(fn_params) ++ fun_internal_ADC.(fn_vars)) e m0' ->
    bind_parameters e m0' fun_internal_ADC.(fn_params) vargs m0'' ->
    eval_expression (Genv.globalenv prog_adc) e m hasSPSR t m' v ->
    proc_state_related proc m' e (Ok tt (mk_semstate l b s)) ->
    bool_val v T4 = Some true->
    Arm6_State.mode s = exn  em.
Proof.
Admitted.

Lemma hasSPSR_false :
  forall e m t m' v s,
    eval_expression (Genv.globalenv prog_adc) e m hasSPSR t m' v ->
    bool_val v T4 = Some false ->
    Arm6_State.mode s = usr.
Proof.
Admitted.


Definition cp_SR :=
  Ecall
  (Evalof (Evar copy_StatusRegister T14) T14)
  (Econs
    (Eaddrof
      (Efield
        (Ederef (Evalof (Evar adc_compcert.proc T3) T3) T6)
        cpsr T7) T8)
    (Econs
      (Ecall (Evalof (Evar spsr T15) T15)
        (Econs (Evalof (Evar adc_compcert.proc T3) T3)
          Enil) T8) Enil)) T12.

Lemma same_cp_SR :
  forall e m l b s t m' v em,
    proc_state_related proc m e (Ok tt (mk_semstate l b s)) ->
    eval_expression (Genv.globalenv prog_adc) e m cp_SR t m' v ->
    (forall l b, proc_state_related proc m' e
      (Ok tt (mk_semstate l b
      (Arm6_State.set_cpsr s (Arm6_State.spsr s em))))).
Proof.
  intros until em. intros psrel cpsr l' b'.
  inversion cpsr. subst. rename H into ee,H0 into esrv. unfold cp_SR in ee.
  Time inv_eval_expr m m'.
  (* Function spsr, get spsr from the current state *)
  apply (functions_behavior_ok e l b s vf0 fd0 m vargs0 t9 m3 vres0 l b s)
    in psrel; [idtac|exact Heqff0|exact ev_funcall].
  (* Function copy_StatusRegister, copy the current spsr to cpsr*)
  apply (functions_behavior_ok e l b s vf fd m3 vargs t2 m' vres l' b'
    (Arm6_State.set_cpsr s (Arm6_State.spsr s em))) in psrel;
  [idtac|exact Heqff|exact ev_funcall0].
  exact psrel.
Qed.
  

Lemma same_cp_SR_old :
  forall e m l b s t m' v em,
    proc_state_related proc m e (Ok tt (mk_semstate l b s)) ->
    eval_expression (Genv.globalenv prog_adc) e m cp_SR t m' v ->
    (forall l b, proc_state_related proc m' e
      (Ok tt (mk_semstate l b
      (Arm6_State.set_cpsr s (Arm6_State.spsr s em))))).
Proof.
  intros until em. intros psrel cpsr l' b'.
  inv cpsr. 
  Time (  
  inv H; inv H4; inv H9;
  inv H5; inv H4; inv H5; inv H15; inv H4; inv H5;
  inv H14; inv H4; inv H3; inv H15; inv H5; inv H4; inv H5; inv H21;
  inv H13).
  simpl in *.
  (* Function spsr, get spsr from the current state *)
  apply (functions_behavior_ok e l b s vf0 fd0 m4 vargs0 t5 m2 vres0 l b s) 
    in psrel; [idtac|exact H18|exact H23].
  (* Function copy_StatusRegister, copy the current spsr to cpsr*)
  apply (functions_behavior_ok e l b s vf fd m2 vargs t3 m' vres l' b'
    (Arm6_State.set_cpsr s (Arm6_State.spsr s em)))
    in psrel; [idtac|exact H11|exact H16].
  exact psrel.
Qed.

(* Lemma on proc_state_relates holds after unpredictable*)
(* In fact, unpredictable in simlight is a annotation, which will print
   a error message. 
   For the moment, we consider it as a function call with an 
   empty body *)
Definition unpred :=
  Ecall
  (Evalof
    (Evar adc_compcert.unpredictable T16)
    T16) Enil T12.

Lemma same_unpred :
  forall e m s t m' v,
    proc_state_related proc m e (Ok tt s) ->
    eval_expression (Genv.globalenv prog_adc) e m unpred t m' v ->
    proc_state_related proc m' e (Ko Arm6_Message.EmptyMessage).
Proof.
  intros until v. intros psrel unp.
  inv unp. inv H. inv H4. inv H9. inv H5.
  apply (funct_unpredictable e s vf fd m2 vargs t3 m' vres) in psrel;
  unfold unpredictable in psrel; unfold raise in psrel; 
  [exact psrel|exact H11|exact H16].
Qed.

(* Lemma on proc_state_relates holds after NZCV flag setting*)
Definition nflag_assgnt:=
  Eassign
  (Efield
    (Efield
      (Ederef (Evalof (Evar adc_compcert.proc T3) T3) T6)
      cpsr T7) N_flag T10)
  (Ecall (Evalof (Evar get_bit T17) T17)
    (Econs
      (Ecall (Evalof (Evar reg T2) T2)
        (Econs (Evalof (Evar adc_compcert.proc T3) T3)
          (Econs 
            (Evalof (Evar d T4) T4) Enil))
        T1)
      (Econs (Eval (Vint (repr 31)) T9)
        Enil)) T10) T10.

Lemma same_nflag_assgnt :
  forall e m l b s d t m' v,
  proc_state_related proc m e (Ok tt (mk_semstate l b s)) ->
  d_func_related m e d ->
  eval_expression (Genv.globalenv prog_adc) e m nflag_assgnt t m' v->
  forall l b,
  proc_state_related proc m' e
    (Ok tt
        (mk_semstate l b
           (Arm6_State.set_cpsr_bit s Nbit
              (Arm6_State.reg_content s d) [n31] )
         )
    ).
Proof.
Admitted.

Definition zflag_assgnt :=
  Eassign
  (Efield
    (Efield
      (Ederef 
        (Evalof (Evar adc_compcert.proc T3) T3) T6)
      cpsr T7) Z_flag T10)
  (Econdition
    (Ebinop Oeq
      (Ecall (Evalof (Evar reg T2) T2)
        (Econs
          (Evalof (Evar adc_compcert.proc T3) T3)
          (Econs
            (Evalof (Evar d T4) T4)
            Enil)) T1)
      (Eval (Vint (repr 0)) T9) T9)
    (Eval (Vint (repr 1)) T9)
    (Eval (Vint (repr 0)) T9) T9) T10.

Lemma same_zflag_assgnt :
  forall e m l b s d t m' v,
    proc_state_related proc m e (Ok tt (mk_semstate l b s)) ->
    d_func_related m e d ->
    eval_expression (Genv.globalenv prog_adc) e m zflag_assgnt t m' v->
    forall l b, proc_state_related proc m' e 
      (Ok tt (mk_semstate l b (Arm6_State.set_cpsr_bit s Zbit
        (if Util.zeq (Arm6_State.reg_content s d) 0
         then repr 1
         else repr 0)))).
Proof.
Admitted.

Definition cflag_assgnt:=
  Eassign
  (Efield
    (Efield
      (Ederef
        (Evalof (Evar adc_compcert.proc T3) T3)
        T6) cpsr T7) C_flag T10)
  (Ecall
    (Evalof 
      (Evar CarryFrom_add3 T18) T18)
    (Econs
      (Evalof (Evar old_Rn T1) T1)
      (Econs
        (Evalof
          (Evar shifter_operand T1)
          T1)
        (Econs
          (Evalof
            (Efield
              (Efield
                (Ederef
                  (Evalof (Evar adc_compcert.proc T3) T3)
                  T6) cpsr T7) C_flag T10)
            T10) Enil))) T10) T10.

Lemma same_cflag_assgnt:
  forall m e l b s0 s n so t m' v,
    proc_state_related proc m e (Ok tt (mk_semstate l b s)) ->
    n_func_related m e n ->
    so_func_related m e so ->
    eval_expression (Genv.globalenv prog_adc) e m cflag_assgnt t m' v->
    forall l b, proc_state_related proc m' e
      (Ok tt (mk_semstate l b (Arm6_State.set_cpsr_bit s Cbit
        (Arm6_Functions.CarryFrom_add3 (Arm6_State.reg_content s0 n) so
          (Arm6_State.cpsr (st (mk_semstate l b s))) [Cbit])))).
Proof.
Admitted.

Definition vflag_assgnt:=
  Eassign
  (Efield
    (Efield
      (Ederef
        (Evalof (Evar adc_compcert.proc T3) T3)
        T6) cpsr T7) V_flag T10)
  (Ecall
    (Evalof
      (Evar OverflowFrom_add3 T19)
      T19)
    (Econs
      (Evalof (Evar old_Rn T1) T1)
      (Econs
        (Evalof
          (Evar shifter_operand T1)
          T1)
        (Econs
          (Evalof
            (Efield
              (Efield
                (Ederef
                  (Evalof (Evar adc_compcert.proc T3) T3)
                  T6) cpsr T7) C_flag T10)
            T10) Enil))) T10) T10.

Lemma same_vflag_assgnt:
  forall m e l b s0 s n so t m' v,
    proc_state_related proc m e (Ok tt (mk_semstate l b s)) ->
    n_func_related m e n ->
    so_func_related m e so ->
    eval_expression (Genv.globalenv prog_adc) e m vflag_assgnt t m' v->
    proc_state_related proc m' e
      (Ok tt (mk_semstate l b (Arm6_State.set_cpsr_bit s Arm6_SCC.Vbit
        (Arm6_Functions.OverflowFrom_add3 (Arm6_State.reg_content s0 n) so
           (Arm6_State.cpsr (st (mk_semstate l b s))) [Cbit])))).
Proof.
Admitted.


(* During function execution, none other parameters are changed*)
Lemma cp_SR_params_not_changed:
  forall m e v m' i, 
    eval_expression (Genv.globalenv prog_adc) e m cp_SR Events.E0 m' v ->
    param_val i m e = param_val i m' e.
Proof.
Admitted.

Lemma reg_S_not_changed :
  forall e m vargs t m' v,
    eval_funcall (Genv.globalenv prog_adc) m (Internal fun_internal_reg) 
    vargs t m' v ->
    param_val S m e = param_val S m' e.
Proof.
Admitted.

Lemma reg_mem_not_changed:
  forall m vargs t m' v,
    eval_funcall (Genv.globalenv prog_adc) m (Internal fun_internal_reg) 
    vargs t m' v ->
    m = m'.
Proof.
Admitted. 



Lemma rn_ass_params_not_changed:
  forall m e v m' i, 
    eval_expression (Genv.globalenv prog_adc) e m oldrn_assgnt Events.E0 m' v ->
    param_val i m e = param_val i m' e.
Proof.
Admitted.

Lemma set_reg_params_not_changed:
  forall m e v m' i, 
    eval_expression (Genv.globalenv prog_adc) e m set_regpc Events.E0 m' v ->
    param_val i m e = param_val i m' e.
Proof.
Admitted.

Lemma unpred_params_not_changed:
  forall m e v m' i, 
    eval_expression (Genv.globalenv prog_adc) e m unpred Events.E0 m' v ->
    param_val i m e = param_val i m' e.
Proof.
Admitted.

Lemma nf_params_not_changed:
  forall m e v m' i, 
    eval_expression (Genv.globalenv prog_adc) e m nflag_assgnt Events.E0 m' v ->
    param_val i m e = param_val i m' e.
Proof.
Admitted.

Lemma zf_params_not_changed:
  forall m e v m' i, 
    eval_expression (Genv.globalenv prog_adc) e m zflag_assgnt Events.E0 m' v ->
    param_val i m e = param_val i m' e.
Proof.
Admitted.

Lemma vf_params_not_changed:
  forall m e v m' i, 
    eval_expression (Genv.globalenv prog_adc) e m vflag_assgnt Events.E0 m' v ->
    param_val i m e = param_val i m' e.
Proof.
Admitted.

Lemma cf_params_not_changed:
  forall m e v m' i, 
    eval_expression (Genv.globalenv prog_adc) e m cflag_assgnt Events.E0 m' v ->
    param_val i m e = param_val i m' e.
Proof.
Admitted.

Lemma same_bool : forall b, b&&b = b.
Proof.
  destruct b;simpl;reflexivity.
Qed.


Theorem related_aft_ADC: forall e m0 m1 m2 mfin vargs s out sbit cond d n so,
  alloc_variables empty_env m0 (fun_internal_ADC.(fn_params) ++ fun_internal_ADC.(fn_vars)) e m1 ->
  bind_parameters e m1 fun_internal_ADC.(fn_params) vargs m2 ->
(* TODO: valid_access needs to be more precise *)
  (forall m ch b ofs, Mem.valid_access m ch b ofs Readable) ->
  proc_state_related proc m2 e (Ok tt (mk_semstate nil true s)) ->
  sbit_func_related m2 e sbit ->
  cond_func_related m2 e cond ->
  d_func_related m2 e d ->
  n_func_related m2 e n ->
  so_func_related m2 e so ->
(* Comparison between eval_funcall, exec_stmt:
   [eval_funcall] is big step semantic. It can be seen as 6 steps, 
   and we can observe 4 times of memory changes.
   1. Check there are no repetitive parameters in function parameter list;
   2. Allocate function parameters into memory and fill them in the empty local environment (m0->m1);
   3. Bind these parameters with there initial values (m1->m2);
   4. Execute all the statement of the function body (m2->m3);
   5. Clean up the memory which are used to store the local parameters when
   execution finishes (m3->m4).
   This final memory doesn't contain the final [proc] we expect. It is in [m3], but in [m4],
   their memory blocks are freed.
   [exec_stmt] is also big step semantic. It indicates the outcome of 
   statement execution [Out_break], [Out_continue], [Out_normal] and [Out_return].
   The final memory state is the memory which contains the final values of parameters.
   The final [proc] is in this memory state which we want to relate.*)
  exec_stmt (Genv.globalenv prog_adc) e m2 fun_internal_ADC.(fn_body) Events.E0 mfin out ->
  proc_state_related proc mfin e (S.ADC_step sbit cond d n so (mk_semstate nil true s)). 
Proof.
  
  intros until so.
  intros al bi valacc psrel sfrel cfrel dfrel nfrel sofrel exstmt.

  (* expand the whole statement of ADC, from m2 to mfin *)
  inv exstmt; [idtac | nod];
  apply Events.Eapp_E0_inv in H3; destruct H3; subst.
  rename H4 into rn_assgnt, H7 into main_p.
  (* Old_Rn assignment, from m2 to m3 *)
  inv rn_assgnt;
  rename H2 into rn_assgnt.
  (* the projection relation between state and other parameters
     still hold after execute old_rn assignment, from m2 to m3 *)
  apply (oldrn_assgnt_ok e m2 nil true s Events.E0 m3 v) in psrel; 
    [idtac|exact rn_assgnt].
  unfold sbit_func_related in sfrel; unfold bit_proj in sfrel;
  rewrite (rn_ass_params_not_changed m2 e v m3 S) in sfrel;
    [idtac | exact rn_assgnt];
  fold (bit_proj m3 e S) in sfrel; fold (sbit_func_related m3 e sbit) in sfrel.
  unfold cond_func_related in cfrel; unfold cond_proj in cfrel.
  rewrite (rn_ass_params_not_changed m2 e v m3 adc_compcert.cond) in cfrel;
    [idtac | exact rn_assgnt];
  fold (cond_proj adc_compcert.cond m3 e) in cfrel; fold (cond_func_related m3 e cond) in cfrel.
  unfold d_func_related in dfrel; unfold reg_proj in dfrel;
  rewrite (rn_ass_params_not_changed m2 e v m3 adc_compcert.d) in dfrel;
    [idtac | exact rn_assgnt];
  fold (reg_proj m3 e adc_compcert.d) in dfrel; fold (d_func_related m3 e d) in dfrel.
  unfold n_func_related in nfrel; unfold reg_proj in nfrel;
  rewrite (rn_ass_params_not_changed m2 e v m3 adc_compcert.n) in nfrel;
    [idtac | exact rn_assgnt]; 
  fold (reg_proj m3 e adc_compcert.n) in nfrel; fold (n_func_related m3 e n) in nfrel.
  unfold so_func_related in sofrel; unfold bits_proj in sofrel;
  rewrite (rn_ass_params_not_changed m2 e v m3 shifter_operand) in sofrel;
    [clear rn_assgnt | exact rn_assgnt];
  fold (bits_proj m3 e shifter_operand) in sofrel;
  fold (so_func_related m3 e so) in sofrel.
  (* evaluate e *)
  generalize al;intros av.
  inv av. rename H6 into alcb1.
  inv H7. rename H6 into alcb0.
  inv H8. rename H6 into alcb2.
  inv H7. rename H6 into alcb3.
  inv H8. rename H6 into alcb4.
  inv H7. rename H6 into alcb5.
  inv H8. rename H6 into alcb6.
  inv H7.
  pose (e:=
    (PTree.set old_Rn (b6, Tint I32 Unsigned)
      (PTree.set shifter_operand (b5, Tint I32 Unsigned)
        (PTree.set adc_compcert.n (b4, Tint I8 Unsigned)
          (PTree.set adc_compcert.d (b3, Tint I8 Unsigned)
            (PTree.set adc_compcert.cond (b2, Tint I32 Signed)
              (PTree.set S (b0, Tint I8 Signed)
                (PTree.set adc_compcert.proc (b1, Tpointer typ_SLv6_Processor)
                  empty_env))))))));
  fold e in al,bi,sfrel,cfrel,dfrel,nfrel,sofrel,psrel,main_p|-*.
  (* ConditionPassed, from m3 to m4, m3 = m4 m0 e m0' m m' t v,*)
  inv main_p;
  rename H5 into condpass, H8 into cp_b, H9 into main_p, H4 into evs;
  generalize condpass;intro condpass';
      simpl in cp_b;
      apply Events.Eapp_E0_inv in evs; destruct evs; subst;
      apply no_effect_condpass in condpass0;
        [rewrite condpass0 in *;clear condpass0
          |simpl;reflexivity].
      (* ConditionPassed(&proc->cpsr, cond) has the same value as 
         Arm6_Functions.State.ConditionPassed s cond, in m4 *)
      generalize al;intros al'.
      apply condpass_bool with _ _ _ m10 nil true s cond Events.E0 m10 v1 b in al';
        [idtac|exact psrel|exact cfrel|exact condpass'| exact cp_b].
      (* two cases, the boolean value of ConditionPassed *)
      destruct b.
        (* ConditionPassed(&proc->cpsr, cond) evaluates to true *)
        (* set_reg_or_pc, from m4 to m5 *)
        inv main_p; [idtac | nod];
        rename H4 into setreg, H7 into main_p, H3 into evs;
        apply Events.Eapp_E0_inv in evs; destruct evs; subst.
        (* projection relation between state and other parameters after execute
           set_reg_or_pc, from m10 to m11 *)
        inv setreg;
        rename H2 into setreg.
        apply same_setregpc with _ _ _ _ s s Events.E0 m11 v0 d n so 
          nil (Util.zne d 15) in psrel;
          [idtac | fold set_regpc in setreg; apply setreg].
        unfold sbit_func_related in sfrel; unfold bit_proj in sfrel;   
        rewrite (set_reg_params_not_changed m10 e v0 m11 S) in sfrel;
          [idtac | exact setreg];
        fold (bit_proj m11 e S) in sfrel; fold (sbit_func_related m11 e sbit) in sfrel.
        unfold cond_func_related in cfrel; unfold cond_proj in cfrel;
        rewrite (set_reg_params_not_changed m10 e v0 m11 adc_compcert.cond) in cfrel;
          [idtac | exact setreg];
        fold (cond_proj adc_compcert.cond m11 e) in cfrel; fold (cond_func_related m11 e cond) in cfrel.
        unfold d_func_related in dfrel; unfold reg_proj in dfrel;
        rewrite (set_reg_params_not_changed m10 e v0 m11 adc_compcert.d) in dfrel;
          [idtac | exact setreg];
        fold (reg_proj m11 e adc_compcert.d) in dfrel; 
        fold (d_func_related m11 e d) in dfrel.
        unfold n_func_related in nfrel; unfold reg_proj in nfrel;
        rewrite (set_reg_params_not_changed m10 e v0 m11 adc_compcert.n) in nfrel;
          [idtac | exact setreg]; 
        fold (reg_proj m11 e adc_compcert.n) in nfrel;
        fold (n_func_related m11 e n) in nfrel.
        unfold so_func_related in sofrel; unfold bits_proj in sofrel;
        rewrite (set_reg_params_not_changed m10 e v0 m11 shifter_operand) in sofrel;
          [clear setreg | exact setreg];
        fold (bits_proj m11 e shifter_operand) in sofrel;
        fold (so_func_related m11 e so) in sofrel.
        (* S == 1 && d == 15, from m11 to m12, has no effect on memory, m5 = m6 *)
        inv main_p;
          rename H5 into sd, H8 into sd_b, H9 into main_p, H4 into evs;
          generalize sd;intro sd';
          simpl in sd_b;
          apply no_effect_is_S_set_and_is_pc in sd;
          rewrite sd in *;clear sd;
          apply Events.Eapp_E0_inv in evs; destruct evs; subst.
        (* S == 1 && d == 15 has the same value as in Coq side, in m12 *)
        apply (S_pc_bool e m12 Events.E0 m12 v2 sbit d) in sd_b;
        [idtac|exact sfrel|exact dfrel|exact sd'].
        (* two cases on the boolean value of S == 1 && d == 15 *)
        destruct b.
          (* ((S == 1) && (d == 15)) evaluates to true *)
          (* CurrentModeHasSPSR has no effect on memory, from 12 to m13, m12=m13 *)
          inv main_p;
          rename H5 into hasspsr, H8 into spsr_b, H9 into main_p, H4 into evs;
          generalize hasspsr;intro hasspsr1;
            simpl in spsr_b;
            apply Events.Eapp_E0_inv in evs; destruct evs; subst.
            apply if_hasSPSR_ok in hasspsr;
            rewrite hasspsr in *;clear hasspsr.
          (* two cases on the boolean value of CurrentModeHasSPSR *)
          destruct b.
            (* CurrentModeHasSPSR evaluate to true *)
            apply (hasSPSR_true m0 m1 m2 e m13 vargs Events.E0 m13 v3
              nil (Util.zne d 15)
              (Arm6_State.set_reg s d
                (add (add (Arm6_State.reg_content s n) so)
                  (Arm6_State.cpsr s) [Cbit])) und) in spsr_b;
            [idtac |exact al|exact bi|exact hasspsr1|exact psrel].
            (* copy_StatusRegister, from m13 to mfin *)
            inv main_p;
            rename H2 into cp_sr.
            (*generalize psrel; intro psrelm7.*)
            (* projection relation between state and other parameters still hold
               after executing copy_StatusRegister, from m7 to mfin.
               And finally get the projection relation on memory mfin *)
            apply (same_cp_SR e m13 nil (Util.zne d 15) 
              (Arm6_State.set_reg s d
                (add (add (Arm6_State.reg_content s n) so)
                  (Arm6_State.cpsr s) [Cbit])) Events.E0 mfin v4 und) 
            with nil (Util.zne d 15) in psrel;
              [idtac | exact cp_sr ].
            unfold sbit_func_related in sfrel; unfold bit_proj in sfrel;   
            rewrite (cp_SR_params_not_changed m13 e v4 mfin S) in sfrel;
              [idtac | exact cp_sr];
            fold (bit_proj mfin e S) in sfrel;
            fold (sbit_func_related mfin e sbit) in sfrel.
            unfold cond_func_related in cfrel; unfold cond_proj in cfrel;
            rewrite (cp_SR_params_not_changed m13 e v4 mfin adc_compcert.cond) 
              in cfrel;
              [idtac | exact cp_sr];
            fold (cond_proj adc_compcert.cond mfin e) in cfrel;
            fold (cond_func_related mfin e cond) in cfrel.
            unfold d_func_related in dfrel; unfold reg_proj in dfrel;
            rewrite (cp_SR_params_not_changed m13 e v4 mfin adc_compcert.d) in dfrel;
              [idtac | exact cp_sr];
            fold (reg_proj mfin e adc_compcert.d) in dfrel;
            fold (d_func_related mfin e d) in dfrel.
            unfold n_func_related in nfrel; unfold reg_proj in nfrel;
            rewrite (cp_SR_params_not_changed m13 e v4 mfin adc_compcert.n) in nfrel;
              [idtac | exact cp_sr]; 
            fold (reg_proj mfin e adc_compcert.n) in nfrel;
            fold (n_func_related mfin e n) in nfrel.
            unfold so_func_related in sofrel; unfold bits_proj in sofrel;
            rewrite (cp_SR_params_not_changed m13 e v4 mfin shifter_operand) in sofrel;
              [clear cp_sr | exact cp_sr];
            fold (bits_proj mfin e shifter_operand) in sofrel;
            fold (so_func_related mfin e so) in sofrel.
            (* expand ADC_step *)
            unfold S.ADC_step; unfold _get_st; unfold bind_s;
            unfold bind; simpl.
            rewrite al'; rewrite sd_b; simpl.
            unfold if_CurrentModeHasSPSR; unfold block; unfold fold_left;
            unfold _get_bo; unfold bind_s; unfold next; unfold bind; simpl;
            unfold _Arm_State.set_reg.
            rewrite spsr_b; simpl; unfold _Arm_State.set_reg. 
            unfold _Arm_State.set_cpsr;
            unfold _set_bo; unfold ok_semstate; unfold loc; unfold st. 
            rewrite same_bool.
            (* The same projection relation as the one in hypothesis *)
            exact psrel.
            
            (* CurrentModeHasSPSR(proc) evaluates to false *)
            apply (hasSPSR_false e m13 Events.E0 m13 v3
              (Arm6_State.set_reg s d
                (add (add (Arm6_State.reg_content s n) so)
                  (Arm6_State.cpsr s) [Cbit]))) in spsr_b;
            [idtac |exact hasspsr1].
            (* meet unpredictable *)
            inv main_p; rename H2 into unp.
            (* projection relation between state and other parameters still hold
               after unpredictable, from m7 to mfin.*)
            apply (same_unpred e m13
              (mk_semstate nil (Util.zne d 15) (Arm6_State.set_reg s d
                (add (add (Arm6_State.reg_content s n) so)
                  (Arm6_State.cpsr s) [Cbit]))) Events.E0 mfin v4) in psrel;
            [idtac | exact unp].
            unfold sbit_func_related in sfrel; unfold bit_proj in sfrel;   
            rewrite (unpred_params_not_changed m13 e v4 mfin S) in sfrel;
              [idtac | exact unp];
            fold (bit_proj mfin e S) in sfrel; 
            fold (sbit_func_related mfin e sbit) in sfrel.
            unfold cond_func_related in cfrel; unfold cond_proj in cfrel;
            rewrite (unpred_params_not_changed m13 e v4 mfin adc_compcert.cond) 
              in cfrel;
              [idtac | exact unp];
            fold (cond_proj adc_compcert.cond mfin e) in cfrel;
            fold (cond_func_related mfin e cond) in cfrel.
            unfold d_func_related in dfrel; unfold reg_proj in dfrel;
            rewrite (unpred_params_not_changed m13 e v4 mfin adc_compcert.d) 
              in dfrel;
              [idtac | exact unp];
            fold (reg_proj mfin e adc_compcert.d) in dfrel;
            fold (d_func_related mfin e d) in dfrel.
            unfold n_func_related in nfrel; unfold reg_proj in nfrel;
            rewrite (unpred_params_not_changed m13 e v4 mfin adc_compcert.n) in nfrel;
              [idtac | exact unp]; 
            fold (reg_proj mfin e adc_compcert.n) in nfrel;
            fold (n_func_related mfin e n) in nfrel.
            unfold so_func_related in sofrel; unfold bits_proj in sofrel;
            rewrite (unpred_params_not_changed m13 e v4 mfin shifter_operand) 
              in sofrel;
              [clear unp | exact unp];
            fold (bits_proj mfin e shifter_operand) in sofrel;
            fold (so_func_related mfin e so) in sofrel.
            (* expand ADC_step *)
            unfold S.ADC_step; unfold _get_st; unfold bind_s;
            unfold bind; simpl.
            rewrite al'; rewrite sd_b; simpl.
            unfold if_CurrentModeHasSPSR; unfold block; unfold fold_left;
            unfold _get_bo; unfold bind_s; unfold next; unfold bind;
            simpl; unfold _Arm_State.set_reg.
            rewrite spsr_b; simpl.
            (* The same projection relation as the one in hypothesis *)
            exact psrel.
          (* ((S == 1) && (d == 15)) evaluates to false *)
          (* S==1 has no effect on memory m6 = m7 *)
          inv main_p;
          rename H5 into is_s, H8 into s_b, H9 into main_p, H4 into evs;
          generalize is_s;intros is_s';
            simpl in s_b; 
            apply no_effect_is_S_set in is_s;
            rewrite is_s in *;clear is_s;
            apply Events.Eapp_E0_inv in evs; destruct evs; subst.
          (* S==1 has the same result as in Coq in m7 *)
          apply (S_bool m0 e m1 m13 Events.E0 m13 v3 sbit) in s_b;
            [idtac|exact al|exact sfrel|exact is_s'].
          (* two cases on the bool value of S==1 *)
          destruct b.
            (* S == 1 evaluates to true *)
            (* N_flag assignment from m7 to m8 *)
            inv main_p ;[idtac | nod];
            rename H4 into nf, H7 into main_p, H3 into evs;
            apply Events.Eapp_E0_inv in evs; destruct evs; subst.
            (* projection relation between state and other parameters still hold
               after N_flag assignment, from m7 to m8 *)
            inv nf; rename H2 into nf;
            pose (s0 :=  Arm6_State.set_reg s d
                       (add (add (Arm6_State.reg_content s n) so)
                          (Arm6_State.cpsr s) [Cbit]));
            fold s0 in psrel.
            eapply (same_nflag_assgnt e m13 nil (Util.zne d 15)
              s0 d Events.E0 m14 v4) in psrel;
            [idtac | exact dfrel | exact nf].
            unfold sbit_func_related in sfrel; unfold bit_proj in sfrel;   
            rewrite (nf_params_not_changed m13 e v4 m14 S) in sfrel;
              [idtac | exact nf];
            fold (bit_proj m14 e S) in sfrel;
            fold (sbit_func_related m14 e sbit) in sfrel.
            unfold cond_func_related in cfrel; unfold cond_proj in cfrel;
            rewrite (nf_params_not_changed m13 e v4 m14 adc_compcert.cond) in cfrel;
              [idtac | exact nf];
            fold (cond_proj adc_compcert.cond m14 e) in cfrel;
            fold (cond_func_related m14 e cond) in cfrel.
            unfold d_func_related in dfrel; unfold reg_proj in dfrel;
            rewrite (nf_params_not_changed m13 e v4 m14 adc_compcert.d) in dfrel;
              [idtac | exact nf];
            fold (reg_proj m14 e adc_compcert.d) in dfrel;
            fold (d_func_related m14 e d) in dfrel.
            unfold n_func_related in nfrel; unfold reg_proj in nfrel;
            rewrite (nf_params_not_changed m13 e v4 m14 adc_compcert.n) in nfrel;
              [idtac | exact nf]; 
            fold (reg_proj m14 e adc_compcert.n) in nfrel;
            fold (n_func_related m14 e n) in nfrel.
            unfold so_func_related in sofrel; unfold bits_proj in sofrel;
            rewrite (nf_params_not_changed m13 e v4 m14 shifter_operand) in sofrel;
              [clear nf | exact nf];
            fold (bits_proj m14 e shifter_operand) in sofrel;
            fold (so_func_related m14 e so) in sofrel.
            (* Z_flag assignment from m8 to m9 *)
            inv main_p ;[idtac | nod];
            rename H4 into zf, H7 into main_p, H3 into evs;
            apply Events.Eapp_E0_inv in evs; destruct evs; subst.
            (* projection relation between state and other parameters still hold
               after Z_flag assignment, from m8 to m9 *)
            inv zf; rename H2 into zf;
            pose (s1 := Arm6_State.set_cpsr_bit s0 Nbit
              (Arm6_State.reg_content s0 d) [n31]);
            revert psrel; fold s1; intro psrel;
            eapply (same_zflag_assgnt e m14 nil (Util.zne d 15) s1
              d Events.E0 m15 v5) in psrel;
            [idtac| exact dfrel | exact zf].
            unfold sbit_func_related in sfrel; unfold bit_proj in sfrel;   
            rewrite (zf_params_not_changed m14 e v5 m15 S) in sfrel;
              [idtac | exact zf];
            fold (bit_proj m15 e S) in sfrel;
            fold (sbit_func_related m15 e sbit) in sfrel.
            unfold cond_func_related in cfrel; unfold cond_proj in cfrel;
            rewrite (zf_params_not_changed m14 e v5 m15 adc_compcert.cond) in cfrel;
              [idtac | exact zf];
            fold (cond_proj adc_compcert.cond m15 e) in cfrel;
            fold (cond_func_related m15 e cond) in cfrel.
            unfold d_func_related in dfrel; unfold reg_proj in dfrel;
            rewrite (zf_params_not_changed m14 e v5 m15 adc_compcert.d) in dfrel;
              [idtac | exact zf];
            fold (reg_proj m15 e adc_compcert.d) in dfrel;
            fold (d_func_related m15 e d) in dfrel.
            unfold n_func_related in nfrel; unfold reg_proj in nfrel;
            rewrite (zf_params_not_changed m14 e v5 m15 adc_compcert.n) in nfrel;
              [idtac | exact zf]; 
            fold (reg_proj m15 e adc_compcert.n) in nfrel;
            fold (n_func_related m15 e n) in nfrel.
            unfold so_func_related in sofrel; unfold bits_proj in sofrel;
            rewrite (zf_params_not_changed m14 e v5 m15 shifter_operand) in sofrel;
              [clear zf | exact zf];
            fold (bits_proj m15 e shifter_operand) in sofrel; 
            fold (so_func_related m15 e so) in sofrel.
            (* C_flag assignment from m15 to m16 *)
            inv main_p ;[idtac | nod];
            rename H4 into cf, H7 into vf, H3 into evs;
            apply Events.Eapp_E0_inv in evs; destruct evs; subst.
            (* projection relation between state and other parameters still hold
               after C_flag assignment, from m15 to m16 *)
            inv cf; rename H2 into cf;
            pose (s2 := Arm6_State.set_cpsr_bit s1 Zbit
              (if Util.zeq (Arm6_State.reg_content s1 d) 0
                then repr 1
                else repr 0));
            revert psrel; fold s2; intro psrel;
            eapply (same_cflag_assgnt m15 e nil (Util.zne d 15) s s2
              n so Events.E0 m16 v6) in psrel;
            [idtac| exact nfrel | exact sofrel| exact cf]. 
            unfold sbit_func_related in sfrel; unfold bit_proj in sfrel;   
            rewrite (cf_params_not_changed m15 e v6 m16 S) in sfrel;
              [idtac | exact cf];
            fold (bit_proj m16 e S) in sfrel;
            fold (sbit_func_related m16 e sbit) in sfrel.
            unfold cond_func_related in cfrel; unfold cond_proj in cfrel;
            rewrite (cf_params_not_changed m15 e v6 m16 adc_compcert.cond) in cfrel;
              [idtac | exact cf];
            fold (cond_proj adc_compcert.cond m16 e) in cfrel;
            fold (cond_func_related m16 e cond) in cfrel.
            unfold d_func_related in dfrel; unfold reg_proj in dfrel;
            rewrite (cf_params_not_changed m15 e v6 m16 adc_compcert.d) in dfrel;
              [idtac | exact cf];
            fold (reg_proj m16 e adc_compcert.d) in dfrel;
            fold (d_func_related m16 e d) in dfrel.
            unfold n_func_related in nfrel; unfold reg_proj in nfrel;
            rewrite (cf_params_not_changed m15 e v6 m16 adc_compcert.n) in nfrel;
              [idtac | exact cf]; 
            fold (reg_proj m16 e adc_compcert.n) in nfrel;
            fold (n_func_related m16 e n) in nfrel.
            unfold so_func_related in sofrel; unfold bits_proj in sofrel;
            rewrite (cf_params_not_changed m15 e v6 m16 shifter_operand) in sofrel;
              [clear cf | exact cf];
            fold (bits_proj m16 e shifter_operand) in sofrel;
            fold (so_func_related m16 e so) in sofrel.
            (* projection relation between state still hold
               after V_flag assignment, from m16 to mfin *)
            unfold st in psrel.
            inv vf; rename H2 into vf;
            pose (s3 := Arm6_State.set_cpsr_bit s2 Cbit
              (Arm6_Functions.CarryFrom_add3
                (Arm6_State.reg_content s n) so
                (Arm6_State.cpsr s2) [Cbit]));
            revert psrel; fold s3; intro psrel;
            eapply (same_vflag_assgnt m16 e nil (Util.zne d 15) s s3
              n so Events.E0 mfin v7) in psrel;
            [clear vf| exact nfrel | exact sofrel| exact vf].
            (* expand ADC_step, simplifiy all the if else case *)
            unfold S.ADC_step; unfold _get_st; unfold bind_s; unfold bind; simpl.
            rewrite al'; simpl. 
            unfold block; unfold fold_left at 1; unfold next; 
            unfold bind at 1 2; unfold _get_bo at 1;
            unfold bind_s at 1; unfold bind at 1; unfold bind at 1; 
            unfold set_reg; simpl; unfold _Arm_State.set_reg. 
            fold s0.
            rewrite sd_b; rewrite s_b; simpl.
            (* Nflag *)
            unfold bind at 5. unfold _get_bo at 2. unfold bind_s at 1. 
            unfold bind at 5. unfold bind at 5.
            simpl; unfold _Arm_State.set_cpsr_bit at 1. 
            unfold _get_bo at 2. unfold bind_s at 1. unfold bind at 5.
            unfold _set_bo at 1.  simpl. unfold ok_semstate.
            (* Zflag *)
            unfold _get_bo at 2. unfold bind_s at 1. unfold bind at 5.
            unfold bind at 5. simpl; unfold _Arm_State.set_cpsr_bit at 1.
            unfold _get_bo at 2. unfold bind_s at 1. unfold bind at 5.
            simpl. unfold _set_bo at 1. simpl. unfold ok_semstate.
            (* Cflag *)
            unfold _get_bo at 2. unfold bind_s at 1. unfold bind at 5.
            unfold bind at 5. simpl; unfold _Arm_State.set_cpsr_bit at 1.
            unfold _get_bo at 2. unfold bind_s at 1. unfold bind at 5.
            simpl. unfold _set_bo at 1. simpl. unfold ok_semstate.
            (* Vflag *)
            unfold _get_bo at 2. unfold bind_s at 1. unfold bind at 5.
            unfold bind at 5. simpl; unfold _Arm_State.set_cpsr_bit at 1.
            unfold _get_bo at 2. unfold bind_s at 1. unfold bind at 5.
            simpl. unfold _set_bo at 1. simpl. unfold ok_semstate.
            unfold bind at 4. unfold loc at 1. unfold bo at 1. unfold bo at 3.
            unfold st at 1. unfold st at 3.
            unfold bind at 3. unfold loc at 1. unfold bo at 1. unfold bo at 5.
            unfold st at 1. unfold st at 5.
            unfold bind at 2. unfold loc at 1. unfold bo at 1. unfold bo at 9.
            unfold st at 1. unfold st at 9.
            (* simplify the bo and st of semstate *)
            unfold bind at 1. unfold _get_bo at 2. unfold bind_s at 1.
            unfold bind at 1. unfold bo at 1.
            unfold _set_bo at 1. unfold loc at 1. unfold st at 1.
            unfold ok_semstate.
            unfold _get_bo at 1. unfold bind_s at 1. unfold bind at 1.
            unfold loc at 1. unfold bo. unfold st at 1. unfold st.
            fold s1. fold s2. fold s3. unfold st in psrel.
            rewrite same_bool; rewrite same_bool; rewrite same_bool;
            rewrite same_bool; rewrite same_bool.
            (* get the same projection relation as the one in hypothesis *)
            exact psrel.
            (* S == 1 evaluates to false *)
            (* Skip statement from m7 to mfin, m7 = mfin *)
            inv main_p.
            (* expand ADC_step *)
            unfold S.ADC_step; unfold _get_st; unfold bind_s; unfold bind; simpl.
            rewrite al'; rewrite sd_b; rewrite s_b; simpl.
            unfold block. unfold fold_left. unfold next.
            unfold bind at 3. simpl; unfold _Arm_State.set_reg.
            unfold _get_bo at 2. unfold bind_s at 1. unfold _set_bo at 1.
            unfold ok_semstate.
            unfold bind at 3. unfold loc at 1. unfold bo at 1.
            unfold st at 1.
            unfold _get_bo at 1. unfold bind_s at 1. unfold bind at 3.
            unfold bind at 2.
            unfold bind at 2. unfold _get_bo at 1. unfold bind_s at 1.
            unfold bind at 2. unfold _get_bo at 1. unfold bind_s at 1.
            unfold _set_bo at 1. unfold ok_semstate.
            unfold bind at 2.
            unfold bind at 1. unfold loc. unfold bo. unfold st. simpl.
            simpl. rewrite same_bool.
            (* get the same projection relation as the one in hypothesis *)
            exact psrel.
          (* ConditionPassed(&proc->cpsr, cond) evaluates to false *)
          (* Skip statement from m7 to mfin, m7 = mfin *)
          inv main_p.
          (* expand ADC_step *)
          unfold S.ADC_step; unfold _get_st; unfold bind_s; unfold bind; simpl.
          rewrite al'; simpl.
          (* get the same projection relation as the one in hypothesis *)
          exact psrel.
Qed.