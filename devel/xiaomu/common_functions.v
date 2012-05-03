(**
SimSoC-Cert, a toolkit for generating certified processor simulators.

See the COPYRIGHTS and LICENSE files.

For those library functions, we have general lemma for them in this file.
Then these lemmas can be shared in the operation correctness proofs. 
*)


Require Import Globalenvs Memory.
Require Import Csyntax Csem Cstrategy Coqlib Integers Values Maps Errors. 
Require Import Arm6_State Arm6_Proc Arm6_SCC Bitvec Arm6.
Require Import projection.

Require Import Arm6_Simul.
Import I.
Import Arm6_Functions.Semantics.

Require Import my_inversion.
Require Import my_tactic.

(* The CompcertC generator outputs compcert-c file for each instruction.
   Every file will have the declarations for identifiers and types.
   Different file will give different value to the same identifier.
   The proofs on same function calls can't be reused.
   It is better to put these common used function and their proofs in 
   the same place, and give abstruct values to identifiers.
*)

Section Common_fun.

Variable N_flag : positive.
Variable Z_flag : positive.
Variable C_flag : positive.
Variable V_flag : positive.
Variable Q_flag : positive.
Variable J_flag : positive.
Variable GE0 : positive.
Variable GE1 : positive.
Variable GE2 : positive.
Variable GE3 : positive.
Variable E_flag : positive.
Variable A_flag : positive.
Variable I_flag : positive.
Variable F_flag : positive.
Variable T_flag : positive.
Variable mode : positive.
Variable background : positive.

Definition cf_typ_struct_SLv6_StatusRegister := 
  Cnotations.fcons (N_flag, Tint I8 Unsigned)
  (Cnotations.fcons (Z_flag, Tint I8 Unsigned)
    (Cnotations.fcons (C_flag, Tint I8 Unsigned)
      (Cnotations.fcons (V_flag, Tint I8 Unsigned)
        (Cnotations.fcons (Q_flag, Tint I8 Unsigned)
          (Cnotations.fcons (J_flag, Tint I8 Unsigned)
            (Cnotations.fcons (GE0, Tint I8 Unsigned)
              (Cnotations.fcons (GE1, Tint I8 Unsigned)
                (Cnotations.fcons (GE2, Tint I8 Unsigned)
                  (Cnotations.fcons (GE3, Tint I8 Unsigned)
                    (Cnotations.fcons (E_flag, Tint I8 Unsigned)
                      (Cnotations.fcons (A_flag, Tint I8 Unsigned)
                        (Cnotations.fcons
                          (I_flag, Tint I8 Unsigned)
                          (Cnotations.fcons
                            (F_flag, Tint I8 Unsigned)
                            (Cnotations.fcons
                              (T_flag, Tint I8 Unsigned)
                              (Cnotations.fcons
                                (mode, Tint I32 Signed)
                                (Cnotations.fcons
                                  (background,
                                    Tint I32 Unsigned) Fnil)))))))))))))))).

Variable SLv6_StatusRegister : positive.

Definition cf_typ_SLv6_StatusRegister :=
  Tstruct SLv6_StatusRegister cf_typ_struct_SLv6_StatusRegister.

Variable begin : positive.
Variable size : positive.
Variable _end : positive.
Variable mem : positive.

Definition cf_typ_struct_SLv6_MMU :=
  Cnotations.fcons (begin, Tint I32 Unsigned)
  (Cnotations.fcons (size, Tint I32 Unsigned)
    (Cnotations.fcons (_end, Tint I32 Unsigned)
      (Cnotations.fcons (mem, Tpointer (Tint I8 Unsigned)) Fnil))).

Variable SLv6_MMU : positive.

Definition cf_typ_SLv6_MMU := Tstruct SLv6_MMU cf_typ_struct_SLv6_MMU.

Variable mmu_ptr : positive.
Variable cpsr : positive.
Variable spsrs : positive.
Variable cp15 : positive.
Variable id : positive.
Variable user_regs : positive.
Variable fiq_regs : positive.
Variable irq_regs : positive.
Variable svc_regs : positive.
Variable abt_regs : positive.
Variable und_regs : positive.
Variable pc : positive.
Variable jump : positive.

Variable ee_bit : positive.
Variable u_bit : positive.
Variable v_bit : positive.

Definition cf_typ_struct_SLv6_SystemCoproc :=
  Cnotations.fcons (ee_bit, Tint I8 Unsigned)
  (Cnotations.fcons (u_bit, Tint I8 Unsigned)
    (Cnotations.fcons (v_bit, Tint I8 Unsigned) Fnil)).

Variable SLv6_SystemCoproc : positive.

Definition cf_typ_SLv6_SystemCoproc :=
  Tstruct SLv6_SystemCoproc cf_typ_struct_SLv6_SystemCoproc.

Definition cf_typ_struct_SLv6_Processor :=
  Cnotations.fcons (mmu_ptr, Tpointer cf_typ_SLv6_MMU)
  (Cnotations.fcons (cpsr, cf_typ_SLv6_StatusRegister)
    (Cnotations.fcons (spsrs, Tarray cf_typ_SLv6_StatusRegister 5)
      (Cnotations.fcons (cp15, cf_typ_SLv6_SystemCoproc)
        (Cnotations.fcons (id, Tint I32 Unsigned)
          (Cnotations.fcons (user_regs, Tarray (Tint I32 Unsigned) 16)
            (Cnotations.fcons (fiq_regs, Tarray (Tint I32 Unsigned) 7)
              (Cnotations.fcons
                (irq_regs, Tarray (Tint I32 Unsigned) 2)
                (Cnotations.fcons
                  (svc_regs, Tarray (Tint I32 Unsigned) 2)
                  (Cnotations.fcons
                    (abt_regs, Tarray (Tint I32 Unsigned) 2)
                    (Cnotations.fcons
                      (und_regs, Tarray (Tint I32 Unsigned) 2)
                      (Cnotations.fcons
                        (pc, Tpointer (Tint I32 Unsigned))
                        (Cnotations.fcons 
                          (jump, Tint I8 Unsigned) Fnil)))))))))))).

Variable SLv6_Processor : positive.

Definition cf_typ_SLv6_Processor := 
  Tstruct SLv6_Processor cf_typ_struct_SLv6_Processor.

Definition cf_T1 :=
  Tfunction
  (Tcons (Tpointer cf_typ_SLv6_StatusRegister) 
    (Tcons (Tint I32 Signed) Tnil))
  (Tint I8 Signed).

Definition cf_T2 := Tpointer cf_typ_SLv6_Processor.

Definition cf_T3 := cf_typ_SLv6_Processor.

Definition cf_T4 := cf_typ_SLv6_StatusRegister.

Definition cf_T5 := Tpointer cf_typ_SLv6_StatusRegister.

Definition cf_T6 := Tint I32 Signed.

Definition cf_T7 := Tint I8 Signed.
  
Definition cf_T8 := Tint I32 Unsigned.

Definition cf_T9 := Tint I8 Unsigned.

Definition cf_T10 :=
  Tfunction
  (Tcons (Tpointer cf_typ_SLv6_Processor)
    (Tcons (Tint I8 Unsigned) Tnil)) (Tint I32 Unsigned).

Definition cf_T11 :=
  Tfunction
  (Tcons (Tpointer cf_typ_SLv6_Processor)
    (Tcons (Tint I8 Unsigned) (Tcons (Tint I32 Unsigned) Tnil))) Tvoid.

Definition cf_T12 := Tvoid.

Variable proc : positive.
Variable cond :positive.
Variable ConditionPassed : positive.
Variable shifter_operand :positive.

(* ConditionPassed *)

Definition condpass :=
  Ecall (Evalof (Evar ConditionPassed cf_T1) cf_T1)
  (Econs
    (Eaddrof
      (Efield (Ederef (Evalof (Evar proc cf_T2) cf_T2) cf_T3) cpsr cf_T4)
      cf_T5)
    (Econs (Evalof (Evar cond cf_T6) cf_T6) Enil)) cf_T7.

Definition fun_ConditionPassed :=
  (ConditionPassed, External
    (AST.EF_external ConditionPassed 
      {| AST.sig_args := AST.Tint :: AST.Tint :: nil; 
        AST.sig_res := Some AST.Tint |})
    (Tcons (Tpointer cf_typ_SLv6_StatusRegister) (Tcons (Tint I32 Signed) Tnil))
    cf_T7).

Lemma no_effect_condpass :
  forall ge m vargs t m' v,
    eval_funcall ge m
    (External
      (AST.EF_external ConditionPassed
        {|
          AST.sig_args := AST.Tint :: AST.Tint :: nil;
          AST.sig_res := Some AST.Tint |})
      (Tcons (Tpointer cf_typ_SLv6_StatusRegister)
        (Tcons (Tint I32 Signed) Tnil)) 
      (Tint I8 Signed)) vargs t m' v ->
    m = m'.
Proof.
  intros until v; intro evfunc. 
  inv evfunc. rename H7 into excall.
  inv excall.
  reflexivity.
Qed.

Lemma condpass_bool :
  forall e m l b s cond t m' v bv,
    e!ConditionPassed = None ->
    proc_state_related m e (Ok tt (mk_semstate l b s)) ->
    cond_func_related m e cond ->
    eval_expression (Genv.globalenv prog_adc) e m condpass t m' v ->
    bool_val v cf_T4 = Some b ->
    Arm6_Functions.State.ConditionPassed s cond = bv.
Proof.
Admitted.



(* reg *)

Variable reg : positive.

Definition reg_r id :=
  Ecall (Evalof (Evar reg cf_T10) cf_T10)
  (Econs (Evalof (Evar proc cf_T2) cf_T2)
    (Econs 
      (Evalof (Evar id cf_T9) cf_T9) Enil)) cf_T8.

Lemma same_result_reg_content :
  forall m e l b st rg r ge v,
    proc_state_related m e (Ok tt (mk_semstate l b st)) ->
    reg_proj m e rg = r ->
    eval_simple_rvalue ge e m (reg_r rg) (Vint v) ->
    v = Arm6_State.reg_content st r.
Proof.  
Admitted.

Lemma proc_state_not_changed_reg_content :
  forall m e l b st ge rg t m' a',
    proc_state_related m e (Ok tt (mk_semstate l b st)) ->
    eval_expr ge e m RV (reg_r rg) t m' a' ->
    param_val proc m e = param_val proc m' e.
Proof.
Admitted.    

(* set_reg_or_pc *)

Variable old_Rn :positive.
Variable d :positive.
Variable set_reg_or_pc : positive.

(*
Definition add_old_Rn_so_Cf := 
  (Ebinop Oadd
    (Ebinop Oadd
      (Evalof (Evar old_Rn cf_T8) cf_T8)
      (Evalof (Evar shifter_operand cf_T8) cf_T8)
      cf_T8)
    (Evalof
      (Efield
        (Efield
          (Ederef
            (Evalof (Evar proc cf_T2) cf_T2)
            cf_T6) cpsr cf_T9) C_flag cf_T7) cf_T7)
    cf_T7).
*)

Definition set_regpc src :=
  Ecall (Evalof (Evar set_reg_or_pc cf_T11) cf_T11)
  (Econs (Evalof (Evar proc cf_T2) cf_T2)
    (Econs (Evalof (Evar d cf_T9) cf_T9)
      (Econs src Enil))) cf_T12.

Lemma same_set_reg_or_pc :
  forall e m l b s rd ge src t m' a' v,
    proc_state_related m e (Ok tt (mk_semstate l b s)) ->
    d_func_related m e rd ->
    eval_expr ge e m RV (set_regpc src) t m' a' ->
    eval_simple_rvalue ge e m (set_regpc src) (Vint v) ->
    (forall l b, proc_state_related m' e 
      (Ok tt (mk_semstate l b
        (Arm6_State.set_reg s rd v)))).
Proof.
Admitted.

(* set_reg *)

Variable set_reg : positive.

Definition set_reg_number nm src :=
  Ecall (Evalof (Evar set_reg cf_T11) cf_T11)
  (Econs (Evalof (Evar proc cf_T2) cf_T2)
    (Econs (Eval (Vint (repr nm)) cf_T6)
      (Econs src Enil))) cf_T12.

Lemma same_set_reg_number :
  forall m e l b s ge rg src t m' a' v,
    proc_state_related m e (Ok tt (mk_semstate l b s)) ->
    eval_expr ge e m RV (set_reg_number rg src) t m' a' ->
    eval_simple_rvalue ge e m (set_reg_number rg src) (Vint v) ->
    (forall l b,proc_state_related m' e
      (Ok tt (mk_semstate l b 
        (Arm6_State.set_reg s (mk_regnum rg) v)))).
Proof.
Admitted.

Definition set_reg_ref r src :=
  Ecall (Evalof (Evar set_reg cf_T11) cf_T11)
  (Econs (Evalof (Evar proc cf_T2) cf_T2)
    (Econs (Evalof (Evar r cf_T9) cf_T9)
      (Econs src Enil))) cf_T12.

Lemma same_set_reg_ref :
  forall m e l b s ge rg r src t m' a' v,
    proc_state_related m e (Ok tt (mk_semstate l b s)) ->
    reg_proj m e rg = r ->
    eval_expr ge e m RV (set_reg_ref rg src) t m' a' ->
    eval_simple_rvalue ge e m (set_reg_ref rg src) (Vint v) ->
    (forall l b,proc_state_related m' e
      (Ok tt (mk_semstate l b 
        (Arm6_State.set_reg s (mk_regnum r) v)))).
Proof.
Admitted.

(* set_pc_raw *)

Variable set_pc_raw :positive.

Definition cf_T13 :=
  Tfunction
  (Tcons (Tpointer cf_typ_SLv6_Processor)
    (Tcons (Tint I32 Unsigned) Tnil)) Tvoid.
  

Definition set_pc_raw_src src :=
  Ecall (Evalof (Evar set_pc_raw cf_T13) cf_T13)
  (Econs (Evalof (Evar proc cf_T2) cf_T2)
    (Econs src Enil)) cf_T12.

Lemma same_set_pc_raw :
  forall m e l b s ge t m' a' src v,
    proc_state_related m e (Ok tt (mk_semstate l b s)) ->
    eval_expr ge e m RV (set_pc_raw_src src) t m' a' ->
    eval_simple_rvalue ge e m (set_pc_raw_src src) (Vint v) ->
    (forall l b,proc_state_related m' e
      (Ok tt (mk_semstate l b 
        (Arm6_State.set_reg s PC v)))).
Proof.
Admitted.


End Common_fun.

(* Calling to a external function *)

(* The semantics of system call tells us, that any call to external function 
   will not change the current memory state *)

Lemma mem_not_changed_ef :
  forall ge m nm sg tplst tp vargs t m' v,
    eval_funcall ge m (External (AST.EF_external nm sg) tplst tp) vargs t m' v ->
    m = m'.
Proof.
  intros until v. intro evfun.
  inv evfun. simpl in H7.
  destruct H7.
  reflexivity.
Qed.


(* Calling to an internal function, from memory state m to m'. 
   alloc_variables m to m1;
   bind_parameters m1 to m2;
   exect_stmt m2 to m3;
   free_list m3 to m'.
   If there is no change from m2 to m3, the result to free_list gives the
   same result (m = m') *)

(*
Lemma free_list_to_initialst :
  forall ps_n vs_n ps vs m e m1 vargs m2 bd t out m' rt v,
    list_norepet (ps_n ++ vs_n) ->
    alloc_variables empty_env m (ps ++ vs) e m1 ->
    bind_parameters e m1 ps vargs m2 ->
    exec_stmt ge e m2 bd t m2 out ->
    outcome_result_value out rt v ->
    Mem.free_list m2 (blocks_of_env e) = Some m'.
*)

(*
Lemma free_list_all_some :
  forall m lst m',
    Mem.free_list m lst = Some m' ->
    (forall b lo hi, In (b, lo, hi) lst ->
      exists mi mj, Mem.free mi b lo hi = Some mj).
*)

(*
Lemma free_list_to_initial :
  forall b lo hi ofs e lst m m' ty,
    ~(In (b,lo,hi) lst) ->
    (blocks_of_env e) = lst ->
    Mem.free_list m lst = Some m'->
    load_value_of_type ty m b ofs =
    load_value_of_type ty m' b ofs.
Proof.
  intros until ty. intros not_in boe fl.
  destruct lst.
   simpl in fl.
   injection fl;intros;subst;clear fl.
   reflexivity.

   unfold load_value_of_type;simpl.
   destruct (access_mode ty);try reflexivity.
   symmetry.

   case_eq (Mem.free_list m (p :: lst));
   [intros m1 fls|intros n;rewrite n in fl;clear n;discriminate].  

   apply (Mem.load_free m b lo hi m').
   admit. left. 
*)
    

(* Equivalence of arithmetic definitions *)
Lemma eq_getbit :
  forall x n ,
    0 < n < Z_of_nat wordsize ->
    sign_ext 8 (and (shru x (repr n)) (repr 1)) = x [nat_of_Z n].
Admitted.

(* Finding a function in globalenv *)
(*
Lemma find_f :
  forall ge fid b t m vf,
    Genv.find_symbol ge fid = Some b ->
    load_value_of_type t m b w0 = Some vf ->
    Genv.find_funct ge vf = Some fd
*)

