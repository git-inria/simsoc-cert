Require Import Globalenvs Memory.
Require Import Csyntax Csem Cstrategy Coqlib Integers Values Maps Errors Events.

Require Import Arm6_State Arm6_Proc Arm6_SCC Bitvec Arm6.
Require Import Arm6_Simul.
Import I.
Import Arm6_Functions.Semantics.

(* Auxiliary functions for inversion on type eval_expr *)

(* Constructor eval_val *)
Definition inv_val {g} {e} {m} {ex} {t} {m'} {ex'}
  (ee:eval_expr g e m RV ex t m' ex') :=
  let diag ex ex' m m' :=
    match ex with
      | Eval a b =>
        forall(X:expr->Mem.mem->Prop), X (Eval a b) m -> X ex' m'
      | _ =>True
    end in
    match ee in (eval_expr _ _ m _ ex _ m' ex') return diag ex ex' m m' with
      | eval_val _ _ _ _ => (fun X k => k)
      | _ =>I
    end.

(* Constructor eval_var *)
Definition inv_var {g} {e} {m} {ex} {t} {m'} {ex'}
  (ee:eval_expr g e m LV ex t m' ex') :=
  let diag ex ex' m m' :=
    match ex with
      | Evar a b =>
        forall(X:expr->Mem.mem->Prop),X (Evar a b) m -> X ex' m'
      | _ =>True
    end in
    match ee in (eval_expr _ _ m _ ex _ m' ex') return diag ex ex' m m' with
      | eval_var _ _ _ _ => (fun X k => k)
      | _ => I
    end.

(* Constructor eval_field *)
Definition inv_field {g} {e} {m} {ex} {t} {m'} {ex'}
  (ee:eval_expr g e m LV ex t m' ex') :=
  let diag e ex ex' m m' :=
    match ex with
      | Efield a b c => 
        forall(X:expr->Prop),
          (forall t a',
            eval_expr g e m RV a t m' a' -> X (Efield a' b c)) -> X ex'
      | _ => True
    end in
    match ee in (eval_expr _ e m _ ex _ m' ex') return diag e ex ex' m m' with
      |eval_field _ _ _ t _ a' _ _ H1 =>
        (fun X k => k t a' H1)
      | _ =>I
    end.

(* Constructor eval_valof *)
Definition inv_valof {g} {e} {m} {ex} {t} {m'} {ex'}
  (ee:eval_expr g e m RV ex t m' ex') :=
  let diag e ex ex' m m' :=
    match ex with
      | Evalof a c =>
        forall (X:expr->Prop),
          (forall t a',
            type_is_volatile (typeof a) = false ->
            eval_expr g e m LV a t m' a'->
            X (Evalof a' c)) ->
          (forall t1 a' b ofs t2 v,
            type_is_volatile (typeof a) = true ->
            eval_expr g e m LV a t1 m' a' ->
            eval_simple_lvalue g e m' a' b ofs ->
            deref_loc g (typeof a) m' b ofs t2 v ->
            c = typeof a ->
            X (Eval v c))
          -> X ex'
      | _ =>True
    end in
    match ee in (eval_expr _ e m _ ex _ m' ex')
      return diag e ex ex' m m' with
      |eval_valof _ _ _ t _ a' _ H1 H2 => (fun X k1 k2 => k1 t a' H1 H2)
      |eval_valof_volatile _ _ _ t1 _ a' _ b ofs t2 v H1 H2 H3 H4 H5 =>
        (fun X k1 k2 => k2 t1 a' b ofs t2 v H1 H2 H3 H4 H5)
      | _ => I
    end.

(* Constructor eval_deref *)
Definition inv_deref {g} {e} {m} {ex} {t} {m'} {ex'}
  (ee:eval_expr g e m LV ex t m' ex') :=
  let diag e ex ex' m m' :=
    match ex with
    | Ederef a b =>
      forall (X:expr->Prop),
        (forall t a',
          eval_expr g e m RV a t m' a' -> X (Ederef a' b)) -> X ex'
    | _ => True
    end in
    match ee in (eval_expr _ e m _ ex _ m' ex')
      return diag e ex ex' m m' with
      | eval_deref _ _ _ t _ a' _ H1 =>(fun X k => k t a' H1)
      | _ =>I
    end.

(* Constructor eval_addrof *)
Definition inv_addrof {g} {e} {m} {ex} {t} {m'} {ex'}
  (ee:eval_expr g e m RV ex t m' ex') :=
  let diag e ex ex' m m' :=
  match ex with
    | Eaddrof a b =>
      forall (X:expr->Prop),
        (forall t a',
        eval_expr g e m LV a t m' a' -> X (Eaddrof a' b)) -> X ex'
    | _ =>True
  end in
  match ee in (eval_expr _ e m _ ex _ m' ex')
    return diag e ex ex' m m' with
    | eval_addrof _ _ _ t _ a' _ H1 =>
      (fun X k=> k t a' H1)
    | _ =>I
  end.

(* Constructor eval_unop *)
Definition inv_unop {g} {e} {m} {ex} {t} {m'} {ex'}
  (ee:eval_expr g e m RV ex t m' ex') :=
  let diag e ex ex' m m' :=
    match ex with
      | Eunop a b c =>
        forall (X:expr->Prop),
          (forall t a',
            eval_expr g e m RV b t m' a' -> X(Eunop a a' c))-> X ex'
      | _ => True
    end in
    match ee in (eval_expr _ e m _ ex _ m' ex')
      return diag e ex ex' m m' with
      | eval_unop  _ _ a t _ a' _ ty H=>(fun X k=> k t a' H)
      | _ => I
    end.

(* Constructor eval_binop *)
Definition inv_binop {g} {e} {m} {ex} {t} {m''} {ex'}
  (ee:eval_expr g e m RV ex t m'' ex') :=
  let diag e ex ex' m m'' :=
    match ex with
      | Ebinop a b c d =>
        forall(X:expr->Prop),
          (forall t1 m' a1' t2 a2', 
            eval_expr g e m RV b t1 m' a1' -> 
            eval_expr g e m' RV c t2 m'' a2'->
            X (Ebinop a a1' a2' d)) -> X ex'
      | _ =>True
  end in
    match ee in (eval_expr _ e m _ ex _ m'' ex')
      return diag e ex ex' m m'' with
      |eval_binop _ _ _ t1 m' a1' _ t2 _ a2' _ _ H1 H2 =>
        (fun X k => k t1 m' a1' t2 a2' H1 H2)
      | _ =>I
    end.

(* Constructor eval_condition *)
Definition inv_condition {g} {e} {m} {ex} {t} {m''} {ex'}
  (ee:eval_expr g e m RV ex t m'' ex') :=
  let diag e ex ex' m m'' :=
    match ex with
      | Econdition a1 a2 a3 ty =>
        forall(X:expr->Prop),
          (forall t1 m' a1' v1 t2 a' v' b v,
            simple a2 = false \/ simple a3 = false ->
            eval_expr g e m RV a1 t1 m' a1' ->
            eval_simple_rvalue g e m' a1' v1 ->
            bool_val v1 (typeof a1) = Some b ->
            eval_expr g e m' RV (if b then a2 else a3) t2 m'' a' ->
            eval_simple_rvalue g e m'' a' v' ->
            sem_cast v' (typeof (if b then a2 else a3)) ty = Some v ->
            X (Eval v ty)) -> X ex'
      | _ =>True
    end in
    match ee in (eval_expr _ e m _ ex _ m' ex')
      return diag e ex ex' m m' with
      | eval_condition _ _ _ _ _ _ t1 mi a1' v1 t2 _ a' v' b v H1 H2 H3 H4 H5 H6 H7=>
        (fun X k => k t1 mi a1' v1 t2 a' v' b v  H1 H2 H3 H4 H5 H6 H7)
      | _ => I
    end.

(* Constructior eval_assign *)
Definition inv_assign {g} {e} {m} {ex} {t} {m3} {ex'}
  (ee:eval_expr g e m RV ex t m3 ex') :=
  let diag e ex ex' m m3 :=
    match ex with
      |Eassign l r ty =>
        forall(X:expr->Prop),
          (forall  t1 m1 l' t2 m2 r' b ofs v v' t3,
            eval_expr g e m LV l t1 m1 l'->
            eval_expr g e m1 RV r t2 m2 r' ->
            eval_simple_lvalue g e m2 l' b ofs ->
            eval_simple_rvalue g e m2 r' v ->
            sem_cast v (typeof r) (typeof l) = Some v'->
            assign_loc g (typeof l) m2 b ofs v' t3 m3 ->
            ty = typeof l->
            X (Eval v' ty))->X ex'
          |_=>True
    end in
    match ee in (eval_expr _ e m _ ex _ m' ex')
      return diag e ex ex' m m' with
      | eval_assign _ _ _ _ _ t1 m1 l' t2 m2 r' b ofs v v' t3 _ H1 H2 H3 H4 H5 H6 H7=>
        (fun X k => k t1 m1 l' t2 m2 r' b ofs v v' t3 H1 H2 H3 H4 H5 H6 H7)
      | _ =>I
    end. 

(* Constructor eval_call *)
Definition inv_call {g} {e} {m} {ex} {t} {m'} {ex'}
  (ee:eval_expr g e m RV ex t m' ex') :=
  let diag e ex ex' m m' :=
    match ex with
      | Ecall a b c =>
        forall (X:expr -> Prop),
          (forall t1 m1 rf' t2 m2 rargs' vf vargs targs tres fd t3 vres,
            eval_expr g e m RV a t1 m1 rf' -> 
            eval_exprlist g e m1 b t2 m2 rargs' ->
            eval_simple_rvalue g e m2 rf' vf ->
            eval_simple_list g e m2 rargs' targs vargs ->
            classify_fun (typeof a) = fun_case_f targs tres->
            Genv.find_funct g vf = Some fd ->
            type_of_fundef fd = Tfunction targs tres ->
            eval_funcall g m2 fd vargs t3 m' vres -> 
            X (Eval vres c)) -> X ex'
      | _ => True
    end in
    match ee in (eval_expr _ e m _ ex _ m' ex')
      return diag e ex ex' m m' with
      | eval_call _ _ _ _ _ t1 m1 rf' t2 m2 rargs' vf vargs
        targs tres fd t3 _ vres H1 H2 H3 H4 H5 H6 H7 H8 =>
        (fun X k => k t1 m1 rf' t2 m2 rargs' vf vargs 
          targs tres fd t3 vres H1 H2 H3 H4 H5 H6 H7 H8 )
      | _=> I
    end.

(* Constructor Enil *)
Definition inv_nil {g} {e} {m} {exl} {t} {m'} {exl'}
  (eel:eval_exprlist g e m exl t m' exl') :=
  let diag exl exl' m m' :=
    match exl with
      | Enil =>
        forall (X:exprlist->Mem.mem->Prop),
          X Enil m -> X exl' m'
      | _=> True
    end in
    match eel in (eval_exprlist _ _ m exl _ m' exl')
      return diag exl exl' m m' with
      | eval_nil _ _ => (fun X k => k)
      | _ => I
    end.

(* Constructor Econs *)
Definition inv_cons {g} {e} {m} {exl} {t} {m'} {exl'}
  (eel:eval_exprlist g e m exl t m' exl') :=
  let diag e exl exl' m m' :=
    match exl with
      | Econs a1 al =>
        forall (X:exprlist->Prop),
          (forall t1 m1 a1' t2 al',
            eval_expr g e m RV a1 t1 m1 a1'->
            eval_exprlist g e m1 al t2 m' al'->
            X (Econs a1' al'))-> X exl'
      | _ =>True
    end in
    match eel in (eval_exprlist _ e m exl _ m' exl')
      return diag e exl exl' m m' with
      | eval_cons _ _ _ _ t1 m1 a1' t2 m' al' H1 H2 => 
        (fun X k => k t1 m1 a1' t2 al' H1 H2)
      | _ => I
    end.

(* General inversion tactic on eval_expr from m to m' *)
Ltac inv_eval_expr m m' :=
  let f:=fresh "f" in
  let nexp:=fresh "nexp" in
  let a_:=fresh "a" in
  let a'_:=fresh "a'" in
  let tp_v:=fresh "tp_v" in
  (*ev_funcall*)
  let rf_:=fresh "rf" in
  let t1_:=fresh "t" in
  let t2_:=fresh "t" in
  let t3_:=fresh "t" in
  let m1_:=fresh "m" in
  let m2_:=fresh "m" in
  let rf'_:= fresh "rf'" in
  let rargs'_:=fresh "rargs'" in
  let vf_:=fresh "vf" in
  let vargs_:=fresh "vargs" in
  let targs_:=fresh "targs" in
  let tres_:=fresh "tres" in
  let fd_:=fresh "fd" in
  let vres_:=fresh "vres" in
  let ty_:=fresh "ty" in
  let ev_ex:=fresh "ev_ex" in
  let ev_elst:=fresh "ev_eslst" in
  let esr1:=fresh "esr" in
  let esr2:=fresh "esr" in
  let Heqcf:=fresh "Heqcf" in
  let eslst:=fresh "eslst" in
  let Heqff:=fresh "Heqff" in
  let Heqtf:=fresh "Heqtf" in
  let ev_funcall:=fresh "ev_funcall" in
  (* ev_condition *)
  let a1_:=fresh "a" in
  let a2_:=fresh "a" in
  let v1_:=fresh "v" in
  let v2_:=fresh "v" in
  let v3_:=fresh "v" in
  let b_:=fresh "b" in
  let ev_ex1 := fresh "ev_ex" in
  let ev_ex2 := fresh "ev_ex" in
  let bv := fresh "bv" in
  let semcast:=fresh "semcast" in
  let smpl := fresh "smpl" in
  (* assignment *)
  let ofs_ := fresh "ofs" in
  let esl := fresh "esl" in
  let svot := fresh "svot" in
  (* exprlist *)
  let alst := fresh "alst" in
  match goal with
    |[ee:eval_expr ?ge ?e m ?k ?ex ?et ?m' ?ex'|-?cl]=>
      pose(next_m := m'); pose(next_e := ex');
      change m' with next_m in ee; change ex' with next_e in ee;
      repeat(match goal with [h: context c [m']|-?cl]=>revert h end||idtac);
      repeat(match goal with [h: context c [ex']|-?cl]=> revert h end||idtac);
      unfold next_m,next_e in ee;clear next_m next_e
    |[el:eval_exprlist ?ge ?e m ?rargs ?et ?m' ?rargs' |-?cl]=>
      pose(next_m := m'); pose(next_r := rargs');
      change m' with next_m in el; change rargs' with next_r in el;
      repeat(match goal with [h: context c [m']|-?cl]=>revert h end||idtac);
      repeat(match goal with [h: context c [rargs']|-?cl]=> revert h end||idtac);
      unfold next_m,next_r in el;clear next_m next_r
  end;
  match goal with
    |[ee:eval_expr ?ge ?e m RV (Eval ?v ?ty) ?et m' ?a'|-?cl]=>
      apply (inv_val ee); clear ee; try intros
    |[ee:eval_expr ?ge ?e m LV (Evar ?x ?ty) ?et m' ?a'|-?cl]=>
      apply (inv_var ee); clear ee; try intros
    |[ee:eval_expr ?ge ?e m LV (Efield ?a ?f ?ty) ?t m' ?a'|-?cl]=>
      apply (inv_field ee); clear ee; intros t1_ a1_ ev_ex1; try intros;
      inv_eval_expr m m'
    |[ee:eval_expr ?ge ?e m RV (Evalof ?a ?ty) ?t m' ?a'|-?cl]=>
      apply (inv_valof ee); try discriminate; clear ee; 
      intros t1_ a_ tp_v ev_ex; try intros;
      inv_eval_expr m m'
    |[ee:eval_expr ?ge ?e m LV (Ederef ?a ?ty) ?t m' ?a'|-?cl]=>
      apply (inv_deref ee); clear ee; intros t2_ a2_ ev_ex1; try intros;
      inv_eval_expr m m'
    |[ee:eval_expr ?ge ?e m RV (Eaddrof ?a ?ty) ?t m' ?a'|-?cl]=>
      apply (inv_addrof ee); clear ee; intros t1_ a1_; intros ev_ex1; try intros;
      inv_eval_expr m m'
    |[ee:eval_expr ?ge ?e m RV (Eunop ?op ?a ?ty) ?t m' ?a'|-?cl]=>
      apply (inv_unop ee); clear ee; intros;inv_eval_expr m m'
    |[ee:eval_expr ?ge ?e m RV (Ebinop ?op ?a1 ?a2 ?ty) ?t m' ?a'|-?cl]=>
      apply (inv_binop ee); clear ee; intros t1_ m1_ a1_ t2_ a2_ ev_ex1 ev_ex2;
      try intros;
      try
      (match goal with
        |[ee1:eval_expr ?ge ?e m ?k a1 ?t1 ?mbo ?a1'|-?cl1]=>
          (*if the inversion before may give a equality saying that
             m = m?, and m will be replaced by m?. So the order will
             be, invert the hypothesis related to the lase memory 
             state first, then step backward *)          
          inv_eval_expr mbo m';
          inv_eval_expr m mbo
      end)
    (*|[ee:eval_expr ?ge ?e m RV (Ecast ?a ?ty) ?t m' ?a'|-?cl]=>
      inv ee;inv_eval_expr m m'*)
    |[ee:eval_expr ?ge ?e m RV (Econdition ?a1 ?a2 ?a3 ?ty) ?t m' ?a'|-?cl]=>
      apply (inv_condition ee); clear ee;
      intros t1_ m1_ a1_ v1_ t2_ a2_ v2_ b_ v3_;
      intros smpl ev_ex1 esr1 bv ev_ex2 esr2 semcast;
      try intros;
      try
      (match goal with
        |[ee1: eval_expr ge e m RV a1 ?t1 ?mcond ?a1'|-?cl1]=>
          inv_eval_expr m mcond
      end)
    (*|[ee:eval_expr ?ge ?e m RV (Esizeof ?ty' ?ty) ?t m ?a'|-?cl]=>
      inv ee*)
    |[ee:eval_expr ?ge ?e m RV (Eassign ?l ?r ?ty) ?t m' ?a'|-?cl]=>
      apply (inv_assign ee); clear ee;
      intros t1_ m1_ a1_ t2_ m2_ a2_ b_ ofs_ v1_ v2_ t3_;
      intros ev_ex1 ev_ex2 esl esr1 semcast svot Heqtf;
      try intros;
      try
      (match goal with
        |[ee1:eval_expr ge e m LV l ?t1 ?masgn1 ?l'|-?cl]=>
          try
          (match goal with
            |[ee2:eval_expr ge e masgn1 RV r ?t2 ?masgn2 ?r'|-?cl]=>
              inv_eval_expr masgn1 masgn2;
              inv_eval_expr m masgn1
          end)
      end)
    (*|[ee:eval_expr ?ge ?e m RV (Eassignop ?op ?l ?r ?tyres ?ty) ?t m' ?a'|-?cl]=>
      inv ee;
      try
      (match goal with
        |[ee1:eval_expr ge e m LV l ?t1 ?masgnop1 ?l'|-?cl]=>
          try
          (match goal with
            |[ee2:eval_expr ge e masgnop1 RV r ?t2 ?masgnop2 ?r'|-?cl]=>
              inv_eval_expr masgnop1 masgnop2;
              inv_eval_expr m masgnop1
          end)
      end)
    |[ee:eval_expr ?ge ?e m RV (Epostincr ?id ?l ?ty) ?t m' ?a'|-?cl]=>
      inv ee;
      try
      (match goal with
        |[ee1:eval_expr ge e m LV l t ?mpi ?l'|-?cl]=>
          inv_eval_expr m mpi
      end)
    |[ee:eval_expr ?ge ?e m RV (Ecomma ?r1 ?r2 ?ty) ?t m' ?a'|-?cl]=>
      inv ee;
      match goal with
        |[ee1:eval_expr ge e m RV r1 ?t1 ?mcom ?r1'|-?cl]=>
          inv_eval_expr m mcom; inv_eval_expr mcom m'
      end*)
    |[ee:eval_expr ?ge ?e m RV (Ecall ?rf ?rargs ?ty) ?t m' ?a'|-?cl]=>
      apply (inv_call ee); clear ee;
        intros t1_ m1_ rf'_ t2_ m2_ rargs'_ vf_ vargs_ targs_ tres_ fd_ t3_ 
          vres_;
        intros ev_ex ev_elst esr1 eslst Heqcf Heqff Heqtf 
          ev_funcall; try intros;
      try
      (match goal with
        |[ee1:eval_expr ge e m RV rf ?t1 ?mc1 ?rf'|-?cl]=>
          inv_eval_expr m mc1;
          try
          (match goal with
            |[eel:eval_exprlist ge e ?ml1 ?expr_lst ?t2 ?ml2 ?rargs'|-?cl]=>
              inv_eval_expr ml1 ml2
            | _ => pose (f_cantfind := 0)
          end)
      end)
    |[eel:eval_exprlist ?ge ?e m (Econs ?a1 ?al) ?t m' ?rargs'|-?cl]=>
      apply (inv_cons eel); clear eel;
      intros t1_ m1_ a1_ t2_ alst ev_ex1 ev_elst;
      try intros;
      try
      (match goal with
        |[eel1:eval_expr ge e m RV a1 ?t1 ?ml1 ?a1'|-?cl]=>
          inv_eval_expr ml1 m';
          inv_eval_expr m ml1
        | _ => pose (f_cantfindlist := 0)
      end)
    |[eel:eval_exprlist ?ge ?e m Enil ?t m' ?al'|-?cl]=>
      apply (inv_nil eel); clear eel
    |_=> pose(f:=0)
  end.


(*
Require Import adc_compcert.

Definition condpass :=
  Ecall (Evalof (Evar ConditionPassed T5) T5)
  (Econs
    (Eaddrof
      (Efield (Ederef (Evalof (Evar proc T3) T3) T6) cpsr
        T7) T8) (Econs (Evalof (Evar cond T9) T9) Enil))
  T10.

Lemma no_effect_condpass :
  forall e m m' t v,
    e! ConditionPassed = None ->
    eval_expression (Genv.globalenv p) e m condpass t m' v ->
    m = m'.
Proof.
  intros until v. intros noexists ee.
  inv ee. rename H into ee, H0 into esr.
  unfold condpass in ee.
  (* mem state between m and m' *)
  (*revert esr. apply (inv_call ee). intros. revert H1. apply (inv_valof H); try discriminate.
  clear H. intros t1_ a_ tp_v ev_ex; try intros.
      inv_eval_expr m m1.*)

  inv_eval_expr m m'. intros.
  inversion ev_ex0.
Qed.
*) 

(* simplify the inversion on alloc_variables and bind_parameters definition *)
Ltac inv_alloc_vars hyp e':=
  let ex :=fresh "e" in
  let mx :=fresh "m" in
  let idx :=fresh "id" in
  let tyx :=fresh "ty" in
  let varsx :=fresh "vars" in
  let m1x :=fresh "m1" in
  let b1x :=fresh "b1" in
  let m2x :=fresh "m2" in
  let e2x :=fresh "e2" in
  let alc :=fresh "alc" in
  let nav := fresh "av'" in
  match goal with 
    [h: alloc_variables ?e ?m0 ?lst e' ?m0' |- ?c] =>
    match h with
      | hyp => 
        inversion h as [ex mx|ex mx idx tyx varsx m1x b1x m2x e2x alc nav];
          subst;try clear h;
            (inv_alloc_vars nav e'||idtac)
      |_ => idtac "inversion on alloc_variables fails"
    end
  end.

Ltac inv_bind_params m' :=
  let ex :=fresh "e" in
  let mx :=fresh "m" in
  let idx :=fresh "id" in
  let tyx :=fresh "ty" in
  let paramsx :=fresh "params" in
  let v1x :=fresh "v1" in
  let vlx :=fresh "vl" in
  let bx :=fresh "b" in
  let m1x :=fresh "m1" in
  let m2x :=fresh "m2" in
  let eget :=fresh "eget" in
  let str :=fresh "str" in
  let bp' := fresh "bp'" in
  let Heq := fresh "Heq" in
  match goal with
    [bp: bind_parameters ?ge ?e ?m ?lst ?vlst m' |- ?c] =>
    inversion bp as 
      [ex mx Heq
        |ex mx idx tyx paramsx v1x vlx bx m1x m2x eget str bp'];
    try clear bp;subst;try simpl in eget;
    (inv_bind_params m'|| idtac)
  end.



(*Ltac inv_eval_simple m ex :=
  match goal with
    |[eslst:eval_simple_list ?ge ?e m (Econs ?r ?rl) ?tylst ?vlst|-?cl]=>
      inv eslst;inv_eval_simple m r;inv_eval_simple m rl
    |[eslst:eval_simple_list ?ge ?e m Enil ?t ?rl|-?cl]=>
      inv eslst
    |[esl:eval_simple_lvalue ?ge ?e m (Eloc ?b1 ?ofs1 ?ty) ?b2 ?ofs2|-?cl]=>
      inv esl
    |[esl:eval_simple_lvalue ?ge ?e m (Evar ?x ?ty) ?b ?ofs|-?cl]=>
      inv esl;[try discriminate|try discriminate]
    |[esl:eval_simple_lvalue ?ge ?e m (Ederef ?r ?ty) ?b ?ofs|-?cl]=>
      inv esl;inv_eval_simple r m
    |[esl:eval_simple_lvalue ?ge ?e m (Efield ?l ?f ?ty) ?b ?ofs|-?cl]=>
      inv esl;inv_eval_simple l m
    |[esr:eval_simple_rvalue ?ge ?e m (Eval ?vres ?ty) ?v|-?cl]=>
      inv esr
    |[esr:eval_simple_rvalue ?ge ?e m (Evalof ?l ?ty) ?v|-?cl]=>
      inv esr;inv_eval_simple m l
    |[esr:eval_simple_rvalue ?ge ?e m (Eaddrof ?l ?ty) ?v|-?cl]=>
      inv esr;inv_eval_simple m l
    |[esr:eval_simple_rvalue ?ge ?e m (Eunop ?op ?r1 ?ty) ?v|-?cl]=>
      inv esr;inv_eval_simple m r1
    |[esr:eval_simple_rvalue ?ge ?e m (Ebinop ?op ?r1 ?r2 ?ty) ?v|-?cl]=>
      inv esr;inv_eval_simple m r1;inv_eval_simple m r2
    |[esr:eval_simple_rvalue ?ge ?e m (Ecast ?r1 ?ty) ?v|-?cl]=>
      inv esr;inv_eval_simple m r1
    |[esr:eval_simple_rvalue ?ge ?e m (Esizeof ?ty1 ?ty) ?v|-?cl]=>
      inv esr
  end.
*)
Ltac inv_eval_simple m ex :=
  match goal with
    |[eslst:eval_simple_list ?ge ?e m ex ?tylst ?vlst|-?cl]=>
      match ex with
        |Econs ?r ?rl=>inv eslst;inv_eval_simple m r;inv_eval_simple m rl
        |Enil=>inv eslst
      end
    |[esl:eval_simple_lvalue ?ge ?e m ex ?b ?ofs|-?cl]=>
      match ex with
        |Eloc ?b1 ?ofs1 ?ty=>inv esl
        |Evar ?x ?ty=>inv esl;[try discriminate|try discriminate]
        |Ederef ?r ?ty=>inv esl;inv_eval_simple m r
        |Efield ?l ?f ?ty=>inv esl;inv_eval_simple m l
      end
    |[esr:eval_simple_rvalue ?ge ?e m ex ?v|-?cl]=>
      match ex with
        |Eval ?vres ?ty=>inv esr
        |Evalof ?l ?ty=>inv esr;inv_eval_simple m l
        |Eaddrof ?l ?ty=>inv esr;inv_eval_simple m l
        |Eunop ?op ?r1 ?ty=>inv esr;inv_eval_simple m r1
        |Ebinop ?op ?r1 ?r2 ?ty=>
          inv esr;inv_eval_simple m r1;inv_eval_simple m r2
        |Ecast ?r1 ?ty=>inv esr;inv_eval_simple m r1
        |Esizeof ?ty1 ?ty=>inv esr
      end
  end.


(* Example lemma to test my_inversion *)

Section Test_inv.

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

(* Human readable renaming of [p], which is generated by the Coq printer *)
Definition prog_adc := adc_compcert.p.

(* Timing new inversion on a complex expression *)

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
  intros until v. intros ee.
  inv ee. unfold is_S_set_and_is_pc in H.
  rename H into ee, H0 into esrv.

  (* Old inversion *)
  idtac "using old inversion to discover the relation between m and m'".
  Time (inv ee; inv H3; inv H14; inv H3; inv H15).
  Undo.
  (* New inversion *)
  idtac "using new inversion to discover the relation between m and m'".
  Time (inv_eval_expr m m').

  destruct b.
  
    (* Old inversion *)
    idtac "using old inversion to discover the relation between m and m'".
    Time (inv ev_ex1; inv H3; inv H14; inv H3; inv H15).
    Undo.
    (* New inversion *)
    idtac "using new inversion to discover the relation between m and m'".
    Time (inv_eval_expr m m').
    
    destruct b.

      inv_eval_expr m m'.
      reflexivity.
      inv_eval_expr m m'.
      reflexivity.

    inv_eval_expr m m'.
    reflexivity.
Qed.

(* Timing new inversion on single expression *)

Definition is_S_set :=
  Ebinop Oeq (Evalof (Evar S T10) T10)
    (Eval (Vint (repr 1)) T9) T9.

Lemma no_effect_is_S_set :
  forall e m t m' v,
    eval_expression (Genv.globalenv prog_adc) e m is_S_set t m' v ->
    m = m'.
Proof.
  intros until v. intros is_s. 
  inv is_s. rename H into ee, H0 into esrv. 
  unfold is_S_set in ee.

  (* Old inversion *)
  idtac "using old inversion on Ebinop".
  Time (inv ee).
  Undo.
  (* New inversion *)
  idtac "using new inversion on Ebinop".
  Time (revert esrv; apply (inv_binop ee)).
  clear ee; intros until a2'; intros ee1 ee2 esr.
  
  (* Old inversion *)
  idtac "using old inversion on Evalof".
  Time (inv ee1).
  Undo.
  (* New inversion *)
  idtac "using new inversion on Evalof".
  Time (revert esr; apply (inv_valof ee1)).
  clear ee1; intros until a'0; intros ee esr.
  
  (* Old inversion *)
  idtac "using old inversion on Eval".
  Time (inv ee2).
  Undo.
  (* New inversion *)
  idtac "using new inversion on Eval".
  Time (revert esr; apply (inv_val ee2)).
  clear ee2; intros esr.
  
  (* Old inversion *)
  idtac "using old inversion on Evar".
  Time (inv ee).
  Undo.
  (* New inversion *)
  idtac "using new inversion on Evar".
  Time (revert esr; apply (inv_var ee)).
  clear ee; intros.
  
  reflexivity.
Qed.

End Test_inv.