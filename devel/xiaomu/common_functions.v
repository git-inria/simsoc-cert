Require Import Globalenvs Memory.
Require Import Csyntax Csem Cstrategy Coqlib Integers Values Maps Errors. 
Require Import Arm6_State Arm6_Proc Arm6_SCC Bitvec Arm6.
Require Import projection.

Require Import Arm6_Simul.
Import I.
Import Arm6_Functions.Semantics.

Require Import my_inversion.
Require Import my_tactic.

Section ConditionPass_fun.

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

Definition typ_struct_SLv6_StatusRegister := 
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

Definition typ_SLv6_StatusRegister :=
  Tstruct SLv6_StatusRegister typ_struct_SLv6_StatusRegister.

(*
Definition T1 :=
Tfunction
  (Tcons (Tpointer typ_SLv6_StatusRegister) (Tcons (Tint I32 Signed) Tnil))
  (Tint I8 Signed).

Variable begin : positive.
Variable size : positive.
Variable _end : positive.
Variable mem : positive.

Definition typ_struct_SLv6_MMU :=
  Cnotations.fcons (begin, Tint I32 Unsigned)
  (Cnotations.fcons (size, Tint I32 Unsigned)
    (Cnotations.fcons (_end, Tint I32 Unsigned)
      (Cnotations.fcons (mem, Tpointer (Tint I8 Unsigned)) Fnil))).

Variable SLv6_MMU : positive.

Definition typ_SLv6_MMU := Tstruct SLv6_MMU typ_struct_SLv6_MMU.

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

Definition typ_struct_SLv6_SystemCoproc :=
  Cnotations.fcons (ee_bit, Tint I8 Unsigned)
  (Cnotations.fcons (u_bit, Tint I8 Unsigned)
    (Cnotations.fcons (v_bit, Tint I8 Unsigned) Fnil)).

Variable SLv6_SystemCoproc : positive.

Definition typ_SLv6_SystemCoproc :=
  Tstruct SLv6_SystemCoproc typ_struct_SLv6_SystemCoproc.

Definition typ_struct_SLv6_Processor :=
  Cnotations.fcons (mmu_ptr, Tpointer typ_SLv6_MMU)
  (Cnotations.fcons (cpsr, typ_SLv6_StatusRegister)
    (Cnotations.fcons (spsrs, Tarray typ_SLv6_StatusRegister 5)
      (Cnotations.fcons (cp15, typ_SLv6_SystemCoproc)
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

Definition typ_SLv6_Processor := 
  Tstruct SLv6_Processor typ_struct_SLv6_Processor.

Definition T2 := Tpointer typ_SLv6_Processor.

Definition T3 := typ_SLv6_Processor.

Definition T4 := typ_SLv6_StatusRegister.

Definition T5 := Tpointer typ_SLv6_StatusRegister.

Definition T6 := Tint I32 Signed.

Definition T7 := Tint I8 Signed.

Variable proc : positive.
Variable cond :positive.*)

Variable ConditionPassed : positive.

(*
Definition condpass :=
  Ecall (Evalof (Evar ConditionPassed T1) T1)
  (Econs
    (Eaddrof
      (Efield (Ederef (Evalof (Evar proc T2) T2) T3) cpsr T4)
      T5)
    (Econs (Evalof (Evar cond T6) T6) Enil)) T7.

Definition fun_ConditionPassed :=
  (ConditionPassed, External
    (AST.EF_external ConditionPassed 
      {| AST.sig_args := AST.Tint :: AST.Tint :: nil; 
        AST.sig_res := Some AST.Tint |})
    (Tcons (Tpointer typ_SLv6_StatusRegister) (Tcons (Tint I32 Signed) Tnil))
    T7).
*)

Lemma no_effect_condpass :
  forall ge m vargs t m' v,
    eval_funcall ge m
    (External
      (AST.EF_external ConditionPassed
        {|
          AST.sig_args := AST.Tint :: AST.Tint :: nil;
          AST.sig_res := Some AST.Tint |})
      (Tcons (Tpointer typ_SLv6_StatusRegister)
        (Tcons (Tint I32 Signed) Tnil)) 
      (Tint I8 Signed)) vargs t m' v ->
    m = m'.
Proof.
  intros until v; intro evfunc. 
  inv evfunc. rename H7 into excall.
  inv excall.
  reflexivity.
Qed.

End ConditionPass_fun.

