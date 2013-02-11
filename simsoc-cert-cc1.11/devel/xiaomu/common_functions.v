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
Require Import type_slv6_proc.
(*Require Import adc_compcert_11.*)

(* The CompcertC generator outputs compcert-c file for each instruction.
   Every file will have the declarations for identifiers and types.
   Different file will give different value to the same identifier.
   The proofs on same function calls can't be reused.
   It is better to put these common used function and their proofs in 
   the same place, and give abstruct values to identifiers.
*)

Section Common_fun.

Definition na := noattr.

Definition cf_T1 :=
  Tfunction
  (Tcons (Tpointer typ_SLv6_StatusRegister na) 
    (Tcons (Tint I32 Signed na) Tnil))
  (Tint I8 Signed na).

Definition cf_T2 := Tpointer typ_SLv6_Processor na.

Definition cf_T3 := typ_SLv6_Processor.

Definition cf_T4 := typ_SLv6_StatusRegister.

Definition cf_T5 := Tpointer typ_SLv6_StatusRegister na.

Definition cf_T6 := Tint I32 Signed na.

Definition cf_T7 := Tint I8 Signed na.
  
Definition cf_T8 := Tint I32 Unsigned na.

Definition cf_T9 := Tint I8 Unsigned na.

Definition cf_T10 :=
  Tfunction
  (Tcons (Tpointer typ_SLv6_Processor na)
    (Tcons (Tint I8 Unsigned na) Tnil)) (Tint I32 Unsigned na).

Definition cf_T11 :=
  Tfunction
  (Tcons (Tpointer typ_SLv6_Processor na)
    (Tcons (Tint I8 Unsigned na) (Tcons (Tint I32 Unsigned na) Tnil))) Tvoid.

Definition cf_T12 := Tvoid.

Definition cf_T13 := Tfunction Tnil Tvoid.

Definition cf_T14 := 
  Tfunction (Tcons (Tpointer Tvoid na) (Tcons (Tpointer Tvoid na) Tnil)) cf_T6.

Definition cf_T15 := Tarray cf_T9 81 na.

Definition cf_T16 := Tarray typ_SLv6_StatusRegister 5 na.

Definition cf_T17 := Tfunction (Tcons (Tpointer typ_SLv6_Processor na) Tnil) cf_T7.

Variable proc : positive.
Variable cond :positive.
Variable ConditionPassed : positive.
Variable shifter_operand :positive.

(* Functional relation between the C memory module which contains the other ADC parameters, 
   and the COQ specification of ADC parameters *)
Definition sbit_func_related (m:Mem.mem) (e:env) (sbit:bool):Prop:=
  bit_proj m e adc_compcert.S = sbit.

Definition cond_func_related (m:Mem.mem) (e:env) (cond:opcode):Prop:=
  cond_proj m e = cond.

Definition d_func_related (m:Mem.mem) (e:env) (d:regnum):Prop:=
  reg_proj m e adc_compcert.d = d.

Definition n_func_related (m:Mem.mem) (e:env) (n:regnum):Prop:=
  reg_proj m e adc_compcert.n = n.

Definition so_func_related (m:Mem.mem) (e:env) (so:word):Prop:=
  bits_proj m e shifter_operand = so.

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
    (Tcons (Tpointer typ_SLv6_StatusRegister na) (Tcons (Tint I32 Signed na) Tnil))
    cf_T7).

Lemma no_effect_condpass :
  forall ge m vargs t m' v,
    eval_funcall ge m (snd fun_ConditionPassed) vargs t m' v ->
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
    eval_expression (Genv.globalenv adc_compcert.p) e m condpass t m' v ->
    bool_val v cf_T4 = Some b ->
    Arm6_Functions.State.ConditionPassed s cond = bv.
Proof.
Admitted.

(* spsr *)

Definition fun_internal_CurrentModeHasSPSR :=
  {|fn_return := Tint I8 Signed na;
    fn_params := (proc, Tpointer typ_SLv6_Processor na) :: nil;
    fn_vars := nil;
    fn_body := 
    Sreturn
    (Some
      (Ebinop Olt
        (Evalof
          (Efield
            (Efield
              (Ederef (Evalof (Evar proc cf_T2) cf_T2)
                cf_T3) cpsr cf_T4) mode cf_T7) cf_T7)
        (Eval (Vint (repr 5)) cf_T7) cf_T7)) |}.

Variable CurrentModeHasSPSR : positive.

Definition fun_CurrentModeHasSPSR :=
(CurrentModeHasSPSR, Internal fun_internal_CurrentModeHasSPSR).

Variable printf_ii : positive.
Variable __stringlit_5 : positive.
Variable abort : positive.

Definition fun_internal_spsr :=
  {|fn_return := Tpointer typ_SLv6_StatusRegister na;
    fn_params := (proc, Tpointer typ_SLv6_Processor na) :: nil;
    fn_vars := nil;
    fn_body := 
    Sifthenelse
    (Ecall (Evalof (Evar CurrentModeHasSPSR cf_T17) cf_T17)
      (Econs (Evalof (Evar proc cf_T2) cf_T2) Enil) cf_T7)
    (Sreturn
      (Some (Eaddrof
        (Ederef
          (Ebinop Oadd
            (Evalof
              (Efield
                (Ederef
                  (Evalof (Evar proc cf_T2) cf_T2)
                  cf_T3) spsrs cf_T16) cf_T16)
            (Evalof
              (Efield
                (Efield
                  (Ederef
                    (Evalof (Evar proc cf_T2)
                      cf_T2) cf_T3) cpsr cf_T4) mode cf_T7) cf_T7) cf_T5)
          cf_T4) cf_T5)))
    (Ssequence
      (Sdowhile (Eval (Vint (repr 0)) cf_T7)
        (Ssequence
          (Sdo
            (Ecall (Evalof (Evar printf_ii cf_T14) cf_T14)
              (Econs (Evalof (Evar __stringlit_5 cf_T15) cf_T15)
                (Econs (Eval (Vint (repr 97)) cf_T7) Enil)) cf_T7))
          (Sdo (Ecall (Evalof (Evar abort cf_T13) cf_T13) Enil cf_T12))))
      (Sdo (Ecall (Evalof (Evar abort cf_T13) cf_T13) Enil cf_T12))) |}.



(* reg *)
(*
Variable addr_of_reg_m : positive.

Definition cf_T13 :=
  Tfunction
  (Tcons (Tpointer cf_typ_SLv6_StatusRegister) 
    (Tcons (Tint I32 Signed) Tnil))
  (Tint I32 Unsigned).

Definition cf_T14 :=
  Tfunction
  (Tcons (Tpointer cf_typ_SLv6_Processor) 
    Tnil)
  (Tint I32 Unsigned).
  

Definition fun_addr_of_reg_m :=
  (addr_of_reg_m,
    External
    (AST.EF_external addr_of_reg_m
      {|
        AST.sig_args := AST.Tint :: AST.Tint :: AST.Tint :: nil;
        AST.sig_res := Some AST.Tint |})
    (Tcons (Tpointer cf_typ_SLv6_Processor)
      (Tcons (Tint I8 Unsigned) (Tcons (Tint I32 Signed) Tnil)))
    (Tpointer (Tint I32 Unsigned))).

Variable m : positive.

Definition fun_internal_reg_m :=
  {|fn_return := Tint I32 Unsigned;
    fn_params := (proc, Tpointer cf_typ_SLv6_Processor)
    :: (reg_id, Tint I8 Unsigned)
    :: (m, Tint I32 Signed) :: nil;
    fn_vars := nil;
    fn_body := Sreturn
    (Some
      (Evalof
        (Ederef
          (Ecall (Evalof (Evar addr_of_reg_m cf_T14) cf_T14)
            (Econs (Evalof (Evar proc cf_T9) cf_T9)
              (Econs (Evalof (Evar reg_id cf_T6) cf_T6)
                (Econs (Evalof (Evar m cf_T4) cf_T4) Enil))) cf_T11) cf_T1)
        cf_T1)) |}.

Variable reg_m : positive.

Definition fun_reg_m :=
  (reg_m, Internal fun_internal_reg_m).

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

Definition cf_T15 :=
  Tfunction
  (Tcons (Tpointer cf_typ_SLv6_Processor)
    (Tcons (Tint I32 Unsigned) Tnil)) Tvoid.
  

Definition set_pc_raw_src src :=
  Ecall (Evalof (Evar set_pc_raw cf_T15) cf_T15)
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
*)

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

(* When there is a storage on memory block b changes the value of b,
   the projection variable in formal value changed to the equivalent value*)

(* For variable has just one bit *)
Lemma same_new_bit :
  forall m e idb b (v':bool) m',
    (*bit_proj m e idb = v ->*)
    e!idb=Some(b,Tint I8 Unsigned na) ->
    Mem.store AST.Mint8unsigned m b 0 (Vint v') = Some m' ->
    bit_proj m' e idb = v'.
Proof.
  intros until m'. intros ex ms.
  unfold bit_proj. unfold param_val.
  rewrite ex.
  simpl.
  rewrite Mem.load_store_same with _ m _ _ (Vint v') _;
    [simpl|apply ms].
  destruct v';unfold zero_ext;simpl;lazy;reflexivity.
Qed.
  
(* For variable is a word *)
Lemma same_new_bits :
  forall m e idb b v' m',
    e!idb=Some(b,Tint I32 Unsigned na) ->
    Mem.store AST.Mint32 m b 0 (Vint v') = Some m' ->
    bits_proj m' e idb = v'.
Proof.
  intros until m'. intros ex ms.
  unfold bits_proj. unfold param_val.
  rewrite ex.
  simpl.
  rewrite Mem.load_store_same with _ m _ _ (Vint v') _;
    [simpl;reflexivity|apply ms].
Qed.


(* Calling to an internal function, from memory state m to m'. 
   alloc_variables m to m1;
   bind_parameters m1 to m2;
   exect_stmt m2 to m3;
   free_list m3 to m'.
   If there is no change from m2 to m3, the result to free_list gives the
   same result (m = m') *)

(* Free a block can't bring the memory state back to the original one?*)

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

Lemma int_range :
  forall (i:word),
    0 <= intval i.
Proof.
  intros. destruct i.
  simpl. destruct intrange0. exact H.
Qed.

Lemma eq_getbit :
  forall x n ,
    (and (shru x (repr (Z_of_nat n))) (repr 1)) = x [n].
Proof.
  intros.
  unfold shru.
  induction n.

  simpl Z_of_nat.
  rewrite unsigned_repr;
    [idtac
      |unfold max_unsigned;unfold modulus;unfold two_power_nat;
       unfold shift_nat;simpl iter_nat;omega].
  unfold bit. unfold bits. unfold bits_val. unfold masks.
  simpl masks_aux.
  assert (eqm (Z_of_bits wordsize (bits_of_Z wordsize (unsigned x)) 0)
              (unsigned x)) by (apply Z_of_bits_of_Z).
  apply eqm_small_eq in H;
    [idtac|apply Z_of_bits_range|apply unsigned_range].
  rewrite H.
  rewrite repr_unsigned.
  unfold two_power_nat. unfold shift_nat. simpl iter_nat.
  rewrite Zdiv_1_r.
  rewrite repr_unsigned.
  apply and_commut.
  
  unfold unsigned.
Admitted.

Lemma mult_gt :
  forall x,
    0<=x -> 0<= x* 16777216.
  intros. omega.
Qed.

Lemma shru_two_p :
  forall p,
    shru (repr (two_p (Zpos p))) (repr (Zpos p)) = w1.
Proof.
Admitted.
 
Lemma bsoz_range :
  forall x i,
    bits_of_Z wordsize (repr x) i <= repr 1.
Proof.
  intros.
  case_eq (bits_of_Z wordsize (repr x) i).
  intros. simpl. omega.
  intros. simpl. lazy. intros. discriminate.
Qed.

Lemma eq_getbit' :
  forall x n ,
    0 < n < Z_of_nat wordsize ->  
   min_signed <=
   signed (and (repr (unsigned x / two_p n)) (repr 1)) *
   two_power_pos 24 <= max_signed ->
    sign_ext 8 (and (shru x (repr n)) (repr 1)) = x [nat_of_Z n].
Proof.
  intros x n intval_n intval_n'.
  rewrite sign_ext_shr_shl;
  [idtac
    |unfold wordsize;unfold Wordsize_32.wordsize;simpl;omega].
  rewrite shr_div_two_p.
  rewrite shl_mul_two_p.
  rewrite shru_div_two_p.
  
  (* mul_signed *)
  rewrite mul_signed.
  rewrite unsigned_repr;
    [idtac|
      unfold max_unsigned;unfold modulus;
      unfold wordsize in *;unfold Wordsize_32.wordsize in *;
      unfold two_power_pos in *;simpl in *;
      unfold shift_pos,shift_nat in *;
      simpl iter_pos in *;simpl iter_nat in *;
      change (Zpos (4294967296 - 1)) with (Zpos 4294967295);
      omega].

  change (signed (repr (two_p (unsigned (repr (Z_of_nat wordsize - 8))))))
    with (two_p (unsigned (repr (Z_of_nat wordsize - 8)))).
  simpl.
  destruct intval_n.
  destruct n; try discriminate.
  assert (Z_of_nat wordsize < max_unsigned) by 
    (simpl;unfold max_signed,modulus; lazy; reflexivity).
  rewrite signed_repr; [idtac| assumption].
  rewrite Z_div_mult;
    [idtac
      |unfold two_power_pos;simpl;unfold shift_pos,shift_nat;simpl;omega].
  rewrite repr_signed.
  
  unfold bit, bits, bits_val, masks.
  rewrite minus_diag. simpl masks_aux.
  replace (Zpos p) with (unsigned (repr (Zpos p)));
    [idtac
      |rewrite unsigned_repr;
        [reflexivity|
          assert (Z_of_nat wordsize < max_unsigned);
            [simpl;
             unfold max_unsigned,modulus,wordsize,Wordsize_32.wordsize;simpl;
             unfold shift_pos,shift_nat;simpl;
             change (Zpos (4294967296 - 1)) with (Zpos 4294967295);omega
              |omega]]].

  rewrite <- shru_div_two_p.

  repeat rewrite two_power_nat_two_p.
  rewrite nat_of_Z_eq;
    [idtac
      |assert (unsigned (repr (Zpos p)) = (repr (Zpos p))) 
        by (unfold unsigned; reflexivity);
        unfold unsigned;
        rewrite <- H2;
        rewrite unsigned_repr; [omega| omega]].
  rewrite <- Zpos_eq_Z_of_nat_o_nat_of_P.
  assert ((unsigned (and (repr (two_p (Zpos p))) x)) =
    (repr (unsigned (and (repr (two_p (Zpos p))) x)))) by
  (rewrite repr_unsigned; unfold unsigned; reflexivity).
  assert (unsigned (and (repr (two_p (Zpos p))) x) = and (repr (two_p (Zpos p))) x)
    by (unfold unsigned; reflexivity).
  rewrite <- H3.
  rewrite <- shru_div_two_p.
  rewrite <- and_shru.
  rewrite and_commut.
  rewrite shru_two_p.
  reflexivity.
Qed.  


(* Finding a function in globalenv *)
(*
Lemma find_f :
  forall ge fid b t m vf,
    Genv.find_symbol ge fid = Some b ->
    load_value_of_type t m b w0 = Some vf ->
    Genv.find_funct ge vf = Some fd
*)

Section freelst.
(*
Lemma al_st_fr :
forall m1 lo hi m2 b chunk ofs v m3 m4,
  lo <= ofs < hi ->
  Mem.alloc m1 lo hi = (m2, b) ->
  Mem.store chunk m2 b ofs v = Some m3 ->
  Mem.free m3 b lo hi = Some m4 ->
  m1 = m4.
Proof.
  intros until m4.
Transparent Mem.alloc Mem.store Mem.free.
  unfold Mem.alloc, Mem.store, Mem.free.
  intros ofsrange al st fr (*nb*).
  destruct (Mem.valid_access_dec m2 chunk b ofs Writable); try discriminate.
  destruct (Mem.range_perm_dec m3 b lo hi Freeable); try discriminate.
  injection al; intros bv m2v. clear al.
  injection st; intros m3v. clear st.
  unfold Mem.unchecked_free in fr.
  injection fr; intro m4v. clear fr.


  (* Try to use given Lemma mkmem_ext (in memory.v) to prove m1 = m4 *)
  (* cont1 = cont4 *)
  assert (cont14: Mem.mem_contents m1 b ofs= Mem.mem_contents m4 b ofs).
  rewrite <- m4v; simpl.
  rewrite <- m3v; simpl.
  rewrite <- m2v; simpl.
  rewrite bv.
  rewrite update_s.
  rewrite Mem.clearN_in.
  assert (Mem.perm_order' (Mem.mem_access m1 b ofs) Readable \/
  Mem.mem_contents m1 b ofs = Undef).
  apply Mem.noread_undef.
  destruct H.
  replace (Mem.perm_order' (Mem.mem_access m1 b ofs) Readable)
    with (Mem.perm m1 b ofs Readable) in H;
  [idtac|unfold Mem.perm;reflexivity].
  apply Mem.perm_valid_block in H.
  unfold Mem.valid_block in H.
  rewrite bv in H.
  apply Zlt_not_eq in H.
  destruct H. reflexivity.
  exact H.
  exact ofsrange.

  (* acc1 = acc4 *)
  assert (acc14: Mem.mem_access m1 b ofs = Mem.mem_access m4 b ofs).
  rewrite <- m4v; simpl.
  rewrite update_s.
  unfold zle, zlt.
  destruct ofsrange.
  destruct Z_le_gt_dec; destruct Z_lt_ge_dec; simpl; try congruence.
  destruct (Mem.nextblock_noaccess m1 b).
  rewrite bv in H1.
  info elimtype False. omega.
  apply Mem.bounds_noaccess. rewrite H1; simpl. omega.
  
  (* bound1 = bound4 *)
  assert (bound14: Mem.bounds m1 b = Mem.bounds m4 b).
  destruct (Mem.nextblock_noaccess m1 b).
  destruct H. rewrite bv in H0. apply Zlt_not_eq in H0.
  elimtype False. omega.
  
  destruct (Mem.nextblock_noaccess m4 b).
  
  (*rewrite <- m4v in H0; simpl in H0.
  rewrite <- m3v in H0; simpl in H0.
  rewrite <- m2v in H0; simpl in H0.*)
  

  (*
  rewrite bv.
  rewrite update_s.
  

  destruct (Mem.nextblock_noaccess m4 b).
  *)
Admitted.
*)

End freelst.