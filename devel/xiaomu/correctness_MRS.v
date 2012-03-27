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
Admitted.  
