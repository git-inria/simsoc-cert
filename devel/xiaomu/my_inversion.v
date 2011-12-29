Require Import Globalenvs Memory.
Require Import Csyntax Csem Cstrategy Coqlib Integers Values Maps Errors.
Require Import adc_compcert.
Require Import projection.

Require Import Arm6_State Arm6_Proc Arm6_SCC Bitvec Arm6.
Require Import Arm6_Simul.
Import I.
Import Arm6_Functions.Semantics.

(* Auxiliary functions for inversion on type eval_expr *)

(* Constructor eval_var *)
(*  | eval_var: forall e m x ty,
      eval_expr e m LV (Evar x ty) E0 m (Evar x ty)*)
Definition inv_expr_var ex ex' m m':=
  match ex with
    |Evar a b =>
      forall(X:expr->Mem.mem->Prop),
        X (Evar a b) m -> X ex' m'
    |_=>True
  end.

Ltac inv_var m m' :=
  match goal with [ee:eval_expr ?g ?e m ?rv (Evar ?a ?b) ?t m' ?ex'|-?cl]=>
    generalize 
      (match ee in (eval_expr _ _ m _ ex _ m' ex')
         return inv_expr_var ex ex' m m' with
         |eval_var _ _ _ _ => (fun X k => k)
         |_=>I
       end);
    clear ee; intro k; red in k;
    pose(nm := m');pose(ne:=ex');change m' with nm in k;change ex' with ne in k;
    repeat(match goal with [h:context c [m']|-?cl]=> revert h end||idtac);
    repeat(match goal with [h:context c [ex']|-?cl]=> revert h end||idtac);
    unfold nm,ne in k;clear nm ne;
    apply k; clear k;
    intros
  end.

(* Constructor eval_val *)
Definition inv_expr_val ex ex' m m':=
  match ex with
    |Eval a b =>
      forall(X:expr->Mem.mem->Prop),
        X (Eval a b) m -> X ex' m'
    |_=>True
  end.

Ltac inv_val m m' :=
  match goal with [ee:eval_expr ?g ?e m ?rv (Eval ?a ?b) ?t m' ?ex'|-?cl]=>
    generalize 
      (match ee in (eval_expr _ _ m _ ex _ m' ex')
         return inv_expr_val ex ex' m m' with
         |eval_val _ _ _ _ => (fun X k => k)
         |_=>I
       end);
    clear ee; intro k; red in k;
    pose(nm := m');pose(ne:=ex');change m' with nm in k;change ex' with ne in k;
    repeat(match goal with [h:context c [m']|-?cl]=> revert h end||idtac);
    repeat(match goal with [h:context c [ex']|-?cl]=> revert h end||idtac);
    unfold nm,ne in k;clear nm ne;
    apply k; clear k
  end.

(* Constructor eval_field *)
Definition inv_expr_field g e m ex m' ex' :=
  match ex with
    |Efield a b c => 
      forall(X:expr->Prop),
        (forall t a',
          eval_expr g e m LV a t m' a' -> X (Efield a' b c)) -> X ex'
    |_ => True
  end.

Ltac inv_field m m':=
  match goal with [ee:eval_expr ?g ?e m ?lv (Efield ?a ?f ?ty) ?t m' ?ex'|-?cl]=>
    generalize
      (match ee in (eval_expr _ e m _ ex _ m' ex')
         return inv_expr_field g e m ex m' ex' with
         |eval_field _ _ _ t _ a' _ _ H1 =>
           (fun X k => k t a' H1)
         |_=>I
       end);clear ee;
    intro k; red in k;
    pose(ne:=ex');change ex' with ne in k;
    match goal with [h:context [ex']|-?cl]=>revert h end;
    unfold ne in k;clear ne;
    apply k; clear k
  end.

(* Constructor eval_valof *)
Definition inv_expr_valof g e m ex m' ex' :=
  match ex with
    |Evalof b c =>
      forall (X:expr->Prop),
        (forall t a',
          eval_expr g e m LV b t m' a'->X (Evalof a' c))-> X ex'
    |_=>True
  end.

Ltac inv_valof m m' :=
  match goal with [ee:eval_expr ?g ?e m ?rv (Evalof ?a ?b) ?t m' ?ex'|-?cl]=>
    generalize
      (match ee in (eval_expr _ e m _ ex _ m' ex')
         return inv_expr_valof g e m ex m' ex' with
         |eval_valof _ _ a t _ a' ty H1 =>
           (fun X k => k t a' H1)
         |_=>I
       end);clear ee;
    intro k; red in k;
    pose (ne:=ex'); change ex' with ne in k;
    match goal with [h:context [ex']|-?cl]=>revert h end;
    unfold ne in k; clear ne;
    apply k; clear k
  end.

(* Constructor eval_deref *)
Definition inv_expr_deref g e m ex m' ex' :=
  match ex with
    |Ederef a b =>
      forall (X:expr->Prop),
        (forall t a',
          eval_expr g e m RV a t m' a' -> X (Ederef a' b)) -> X ex'
    |_ => True
  end.

Ltac inv_deref m m':=
  match goal with [ee:eval_expr ?g ?e m  ?lv (Ederef ?a ?ty) ?t m' ?ex'|-?cl]=>
    generalize
      (match ee in (eval_expr _ e m _ ex _ m' ex')
         return inv_expr_deref g e m ex m' ex' with
         |eval_deref _ _ _ t _ a' _ H1 =>
           (fun X k => k t a' H1)
         |_=>I
       end); clear ee;
    intro k; red in k;
    pose (ne:=ex');change ex' with ne in k;
    match goal with [h:context [ex']|-?cl]=>revert h end;
    unfold ne in k ;clear ne;
    apply k;clear k
end.

(* Constructor eval_addrof *)
Definition inv_expr_addrof g e m ex m' ex' :=
  match ex with
    |Eaddrof a b =>
      forall (X:expr->Prop),
        (forall t a',
        eval_expr g e m LV a t m' a' -> X (Eaddrof a' b)) -> X ex'
    |_=>True
  end.

Ltac inv_addrof m m' :=
  match goal with [ee:eval_expr ?g ?e m ?rv (Eaddrof ?a ?ty) ?t m' ?ex'|-?cl]=>
    generalize
      (match ee in (eval_expr _ e m _ ex _ m' ex')
         return inv_expr_addrof g e m ex m' ex' with
         |eval_addrof _ _ _ t _ a' _ H1 =>
           (fun X k=> k t a' H1)
         |_=>I
       end); clear ee;
    intro k; red in k;
    pose(ne:=ex');change ex' with ne in k;
    match goal with [h:context [ex']|-?cl]=>revert h end;
    unfold ne in k;clear ne;
    apply k; clear k
  end.

(* Constructor eval_unop *)
Definition inv_expr_eunop g e m ex m' ex' :=
  match ex with
    |Eunop a b c =>
      forall (X:expr->Prop),
        (forall t a',
          eval_expr g e m RV b t m' a' -> X(Eunop a a' c))-> X ex'
    |_=> True
  end.

(* Constructor eval_binop *)
Definition inv_expr_binop g e m ex m'' ex':=
  match ex with
    |Ebinop a b c d =>
      forall(X:expr->Prop),
        (forall t1 m' a1' t2 a2', 
          eval_expr g e m RV b t1 m' a1' -> 
          eval_expr g e m' RV c t2 m'' a2'->
          X (Ebinop a a1' a2' d)) -> X ex'
    |_=>True
  end.

Ltac inv_binop m m'' :=
  match goal with 
    [ee:eval_expr ?g ?e m ?rv (Ebinop ?op ?a ?b ?ty) ?t m'' ?a'|-?cl]=>
    generalize
      (match ee in (eval_expr _ e m _ ex _ m'' ex')
         return inv_expr_binop g e m ex m'' ex' with
         |eval_binop _ _ _ t1 m' a1' _ t2 m'' a2' _ _ H1 H2 =>
           (fun X k => k t1 m' a1' t2 a2' H1 H2)
         |_=>I
       end); clear ee;
    intro k; red in k;
    pose (ne:=a');change a' with ne in k;
    match goal with [h:context [a']|-?cl]=>revert h end;
    unfold ne in k; clear ne;
    apply k; clear k
  end.
    

(* Constructor eval_condition *)
Definition inv_expr_condition g e m ex m'' ex':=
  match ex with
    |Econdition a1 a2 a3 ty =>
      forall(X:expr->Prop),
        (forall t1 m' a1' v1 t2 a' v' b v,
        eval_expr g e m RV a1 t1 m' a1' ->
        eval_simple_rvalue g e m' a1' v1 ->
        bool_val v1 (typeof a1) = Some b ->
        eval_expr g e m' RV (if b then a2 else a3) t2 m'' a' ->
        eval_simple_rvalue g e m'' a' v' ->
        sem_cast v' (typeof (if b then a2 else a3)) ty = Some v ->
        X (Eval v ty)) -> X ex'
    |_=>True
  end.

Ltac inv_condition m m' :=
  match goal with 
    [ee:eval_expr ?g ?e m ?rv (Econdition ?a1 ?a2 ?a3 ?ty) ?t m' ?ex'|-?cl]=>
    generalize
      (match ee in (eval_expr _ e m _ ex _ m' ex')
         return inv_expr_condition g e m ex m' ex' with
       |eval_condition _ _ _ _ _ _ t1 mi a1' v1 t2 _ a' v' b v H1 H2 H3 H4 H5 H6=>
         (fun X k => k t1 mi a1' v1 t2 a' v' b v  H1 H2 H3 H4 H5 H6)
       |_=> I
     end); clear ee;
    intro k; red in k;
    pose (ne:=ex');change ex' with ne in k;
    match goal with [h:context [ex']|-?cl]=> revert h end;
    unfold ne in k;clear ne;
    apply k; clear k
  end.

(* Constructor eval_sizeof *)
Definition inv_expr_sizeof m ex m' ex':=
  match ex with
    |Esizeof a b =>
      forall(X:Mem.mem->expr->Prop),
        X m (Esizeof a b) -> X m' ex'
    |_=>True
  end.

(* Constructior eval_assign *)
Definition inv_expr_assign g e m ex m3 ex' :=
  match ex with
    |Eassign l r ty =>
      forall(X:expr->Prop),
        (forall  t1 m1 l' t2 m2 r' b ofs v v',
          eval_expr g e m LV l t1 m1 l'->
          eval_expr g e m1 RV r t2 m2 r' ->
          eval_simple_lvalue g e m2 l' b ofs ->
          eval_simple_rvalue g e m2 r' v ->
          sem_cast v (typeof r) (typeof l) = Some v'->
          store_value_of_type (typeof l) m2 b ofs v' = Some m3->
          ty = typeof l->
          X (Eval v' ty))->X ex'
    |_=>True
  end.

Ltac inv_assign m m' :=
  match goal with
    [ee:eval_expr ?g ?e m ?rv (Eassign ?l ?r ?ty) ?t m' ?ex'|-?cl]=>
    generalize
      (match ee in (eval_expr _ e m _ ex _ m' ex')
         return inv_expr_assign g e m ex m' ex' with
         |eval_assign _ _ _ _ _ t1 m1 l' t2 m2 r' b ofs v v' _ H1 H2 H3 H4 H5 H6 H7=>
           (fun X k => k t1 m1 l' t2 m2 r' b ofs v v' H1 H2 H3 H4 H5 H6 H7)
         |_=>I
       end);clear ee;
    intro k; red in k;
    pose(ne:=ex');change ex' with ne in k;
    match goal with [h:context [ex']|-?cl]=> revert h end;
    unfold ne in k;clear ne;
    apply k; clear k
  end.
    

(* Constructor eval_call *)
Definition inv_expr_ecall g e m ex m' ex':=
  match ex with
    |Ecall a b c =>
      forall (X:expr -> Prop),
      (forall rf t1 m1 rf' t2 m2 rargs' vf vargs targs tres fd t3 vres,
      eval_expr g e m RV a t1 m1 rf' -> 
      eval_exprlist g e m1 b t2 m2 rargs' ->
      eval_simple_rvalue g e m2 rf' vf ->
      eval_simple_list g e m2 rargs' targs vargs ->
      classify_fun (typeof rf) = fun_case_f targs tres->
      (*typeof a = Tfunction targs tres ->*)
      Genv.find_funct g vf = Some fd ->
      type_of_fundef fd = Tfunction targs tres ->
      eval_funcall g m2 fd vargs t3 m' vres -> 
      X (Eval vres c)) -> X ex'
    |_=> True
  end.

Ltac inv_call m m' :=
  match goal with
    |[ee:eval_expr ?ge ?e m RV (Ecall ?rf ?rargs ?ty) ?t m' ?a'|-?cl]=>
      generalize 
        (match ee in (eval_expr _ e m _ ex _ m' ex')
           return inv_expr_ecall ge e m ex m' ex' with
           |eval_call _ _ rf rargs typ t1 m1 rf' t2 m2 rargs' vf vargs
             targs tres fd t3 _ vres H1 H2 H3 H4 H5 H6 H7 H8 =>
             (fun X k => k rf t1 m1 rf' t2 m2 rargs' vf vargs 
               targs tres fd t3 vres H1 H2 H3 H4 H5 H6 H7 H8 )
           |_=> I
         end);clear ee;
        intro k;red in k;simpl in k;
        pose(nexp:=a');fold nexp in k;
        match goal with |[es:context [a']|-?cl]=>revert es end;
        unfold nexp in k;clear nexp;apply k;clear k
  end.

(* General inversion tactic on eval_expr from m to m' *)
Ltac inv_eval_expr m m' :=
  let f:=fresh "f" in
  let nexp:=fresh "nexp" in
  let a_:=fresh "a" in
  let a'_:=fresh "a'" in
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
  match goal with
    |[ee:eval_expr ?ge ?e m RV (Econdition ?a1 ?a2 ?a3 ?ty) ?t ?m' ?a'|-?cl]=>
      inv ee;
      match goal with
        |[ee1: eval_expr ge e m RV a1 ?t1 ?mcond ?a1'|-?cl1]=>
          inv_eval_expr m mcond
      end
    |[ee:eval_expr ?ge ?e m RV (Eval ?v ?ty) ?et m' ?a'|-?cl]=>
      inv ee
    |[ee:eval_expr ?ge ?e m LV (Evar ?x ?ty) ?et m' ?a'|-?cl]=>
      inv ee
    |[ee:eval_expr ?ge ?e m RV (Ebinop ?op ?a1 ?a2 ?ty) ?t m' ?a'|-?cl]=>
      (*generalize
        (match ee in (eval_expr _ e m _ ex _ m' ex')
         return inv_expr_binop (Genv.globalenv prog_adc) e m ex m' ex' with
         |eval_binop _ _ a1 t1 m' a1' a2 t2 _ a2' op ty H1 H2 =>
           (fun X k => k t1 m' a1' t2 a2' H1 H2)
         |_=>I
         end);
      intro k;red in k;simpl in k;
      pose(nexp:=a');change a' with nexp in k; 
      match goal with
        |[es:context c [a']|-?cl]=>revert es
        |_=>idtac
      end;
      unfold nexp in k;clear nexp;apply k;clear k;
      intros ;intro ev_ex;intro esr1;*)
    
(*  generalize
      (match H0 in (eval_expr _ e m _ ex _ m' ex')
         return inv_expr_binop (Genv.globalenv prog_adc) e m ex m' ex' with
         |eval_binop _ _ a1 t1 m' a1' a2 t2 _ a2' op ty H1 H2 =>
           (fun X k => k t1 m' a1' t2 a2' H1 H2)
         |_=>I
       end). intro k. red in k. simpl in k. revert H5. apply k.
    intros until a2'. intros expr_a1 expr_a2 esr.*)


      inv ee;
      match goal with
        |[ee1:eval_expr ?ge ?e m ?k a1 ?t1 ?mbo ?a1'|-?cl1]=>
          inv_eval_expr m mbo;inv_eval_expr mbo m'
      end
    |[ee:eval_expr ?ge ?e m RV (Evalof ?a ?ty) ?t m' ?a'|-?cl]=>
      generalize
        (match ee in (eval_expr _ e m _ ex _ m' ex')
           return inv_expr_valof ge e m ex m' ex' with
           |eval_valof _ _ a t _ a' ty H1 =>
             (fun X k => k t a' H1)
           |_=> I
         end);clear ee;
        intro k; red in k;simpl in k;
        pose(nexp:=a');change a' with nexp in k; 
          match goal with
            |[es:context c [a']|-?cl]=>revert es
            |_=>idtac
          end;
          unfold nexp in k;clear nexp;apply k;clear k;
          intros t1_ a_;intro ev_ex;intro esr1;
      (*inv ee;*)inv_eval_expr m m'
    |[ee:eval_expr ?ge ?e m LV (Efield ?a ?f ?ty) ?t m' ?a'|-?cl]=>
      inv ee;inv_eval_expr m m'
    |[ee:eval_expr ?ge ?e m LV (Ederef ?a ?ty) ?t m' ?a'|-?cl]=>
      inv ee;inv_eval_expr m m'
    |[ee:eval_expr ?ge ?e m RV (Eaddrof ?a ?ty) ?t m' ?a'|-?cl]=>
      inv ee;inv_eval_expr m m'
    |[ee:eval_expr ?ge ?e m RV (Eunop ?op ?a ?ty) ?t m' ?a'|-?cl]=>
      inv ee;inv_eval_expr m m'
    |[ee:eval_expr ?ge ?e m RV (Ecast ?a ?ty) ?t m' ?a'|-?cl]=>
      inv ee;inv_eval_expr m m'
    |[ee:eval_expr ?ge ?e m RV (Esizeof ?ty' ?ty) ?t m ?a'|-?cl]=>
      inv ee
    |[ee:eval_expr ?ge ?e m RV (Eassign ?l ?r ?ty) ?t m' ?a'|-?cl]=>
      inv ee;
      match goal with
        |[ee1:eval_expr ge e m LV l ?t1 ?masgn1 ?l'|-?cl]=>
          inv_eval_expr m masgn1;
          match goal with
            |[ee2:eval_expr ge e masgn1 RV r ?t2 ?masgn2 ?r'|-?cl]=>
              inv_eval_expr masgn1 masgn2
          end
      end
    |[ee:eval_expr ?ge ?e m RV (Eassignop ?op ?l ?r ?tyres ?ty) ?t m' ?a'|-?cl]=>
      inv ee;
      match goal with
        |[ee1:eval_expr ge e m LV l ?t1 ?masgnop1 ?l'|-?cl]=>
          inv_eval_expr m masgnop1;
          match goal with
            |[ee2:eval_expr ge e masgnop1 RV r ?t2 ?masgnop2 ?r'|-?cl]=>
              inv_eval_expr masgnop1 masgnop2
          end
      end
    |[ee:eval_expr ?ge ?e m RV (Epostincr ?id ?l ?ty) ?t m' ?a'|-?cl]=>
      inv ee;
      match goal with
        |[ee1:eval_expr ge e m LV l t ?mpi ?l'|-?cl]=>
          inv_eval_expr m mpi
      end
    |[ee:eval_expr ?ge ?e m RV (Ecomma ?r1 ?r2 ?ty) ?t m' ?a'|-?cl]=>
      inv ee;
      match goal with
        |[ee1:eval_expr ge e m RV r1 ?t1 ?mcom ?r1'|-?cl]=>
          inv_eval_expr m mcom; inv_eval_expr mcom m'
      end
    |[ee:eval_expr ?ge ?e m RV (Ecall ?rf ?rargs ?ty) ?t m' ?a'|-?cl]=>
      generalize 
        (match ee in (eval_expr _ e m _ ex _ m' ex')
           return inv_expr_ecall ge e m ex m' ex' with
           |eval_call _ _ rf rargs typ t1 m1 rf' t2 m2 rargs' vf vargs
             targs tres fd t3 _ vres H1 H2 H3 H4 H5 H6 H7 H8 =>
             (fun X k => k rf t1 m1 rf' t2 m2 rargs' vf vargs 
               targs tres fd t3 vres H1 H2 H3 H4 H5 H6 H7 H8 )
           |_=> I
         end);clear ee;
        intro k;red in k;simpl in k;
        pose(nexp:=a');fold nexp in k;
        match goal with
          |[es:context [a']|-?cl]=>revert es
        end;
        unfold nexp in k;clear nexp;apply k;clear k;
        intros rf_ t1_ m1_ rf'_ t2_ m2_ rargs'_ vf_ vargs_ targs_ tres_ fd_ t3_ 
          vres_;
        intros ev_ex ev_elst esr1 eslst Heqcf Heqff Heqtf 
          ev_funcall esr2;
      match goal with
        |[ee1:eval_expr ge e m RV rf ?t1 ?mc1 ?rf'|-?cl]=>
          inv_eval_expr m mc1;
          match goal with
            |[eel:eval_exprlist ge e mc1 ?rargs ?t2 ?mc2 ?rargs'|-?cl]=>
              inv_eval_expr mc1 mc2
          end
      end
    |[eel:eval_exprlist ?ge ?e m (Econs ?a1 ?al) ?t m' ?rargs'|-?cl]=>
      inv eel;
      match goal with
        |[eel1:eval_expr ge e m RV a1 ?t1 ?ml1 ?a1'|-?cl]=>
          inv_eval_expr m ml1; inv_eval_expr ml1 m'
      end
    |[eel:eval_exprlist ?ge ?e m Enil ?t m' ?al'|-?cl]=>
      inv eel
    |_=> pose(f:=0)
  end.

(* simplify the inversion on alloc_variables and bind_parameters definition *)
Ltac inv_alloc_vars e' :=
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
  let av' := fresh "av'" in
  match goal with 
    [av: alloc_variables ?e ?m0 ?lst e' ?m0' |- ?c] => 
    inversion av as [ex mx|ex mx idx tyx varsx m1x b1x m2x e2x alc av'];
    subst;try clear av;
    (inv_alloc_vars e'||idtac)
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
    [bp: bind_parameters ?e ?m ?lst ?vlst m' |- ?c] =>
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


(*
(* Previous experiments with "my_inversion" *)


(* expirement on how to avoid using inversion *)
Ltac gen_inv_S y :=
 pattern y; 
 match goal with [ |- ?concl _ ] => 
   change (match S y with S y => concl y | _ => True end) end;
 cbv beta.

Ltac case_I h := case h; try (intros; exact I); clear h.

Ltac case_h h := case h; clear h; try contradiction.

Ltac rew_clean eq :=
  match type of eq with ?l = ?r => rewrite eq in *; clear eq l end.

Ltac and_eq_subst ae :=
  repeat (rew_clean ae) ||
         (let feq := fresh "eq" in destruct ae as [feq ae];
          rew_clean feq).

Ltac inv_end ev mm mm' :=
   unfold ev, mm, mm' in *; clear ev mm mm'; 
   let ae := fresh "ae" in (intro ae; and_eq_subst ae).

Ltac inv_ecall_begin arg_m ev mm mm' :=
  let e := fresh "expr" in
  let em := fresh "expr_match" in
  match goal with [h : eval_expr _ ?env arg_m _ (Ecall ?a1 ?a2 ?a3) _ ?m' _|- ?c] =>
    pose (e := Ecall a1 a2 a3); 
    pose (ev:=env); pose (mm:=arg_m); pose (mm':=m');
    assert 
      (em : match e with 
                      |Ecall a b c =>
                        (a=a1)/\(b=a2)/\(c=a3)/\(env=ev)/\(arg_m=mm)/\(m'=mm')
                      |_=> False
                    end)
      by repeat (split || reflexivity);
  fold e in h;
  revert em;
  case_h h;
  clear e
  end.

Ltac inv_ecall arg_m t1 m2 rf' t2 m3 rargs' 
         vf vargs0 targs tres fd t3 vres H H0 H1 H2 H3 H4 H5 H6 :=
  let ev:=fresh "ev" in 
  let mm:=fresh "mm" in 
  let mm':=fresh "mm'" in
  inv_ecall_begin arg_m ev mm mm'; 
  intros e0 m1 rf rargs ty t1 m2 rf' t2 m3 rargs' 
         vf vargs0 targs tres fd t3 m4 vres H H0 H1 H2 H3 H4 H5 H6;
  inv_end ev mm mm'.

Ltac inv_evalof_begin arg_m ev mm mm' :=
  let e := fresh "expr" in
  let em := fresh "expr_match" in
  match goal with [h : eval_expr _ ?env arg_m _ (Evalof ?a1 ?a2) _ ?m' _ |- ?c ] =>
    pose (e := Evalof a1 a2); 
    pose (ev:=env); pose (mm:=arg_m); pose (mm':=m');
    assert 
      (em : match e with 
                    |Evalof a b => 
                      (a=a1)/\(b=a2)/\(env=ev)/\(arg_m=mm)/\(m'=mm')
                    |_ => False
                  end)
      by repeat (split || reflexivity);
  fold e in h;
  revert em;
  case_h h;
  clear e
  end.

Ltac inv_evalof arg_m t0 m'0 a' H :=
  let ev:=fresh "ev" in 
  let mm:=fresh "mm" in 
  let mm':=fresh "mm'" in
  inv_evalof_begin arg_m ev mm mm'; 
  intros e0 m1 a t0 m'0 a' ty H;
  inv_end ev mm mm'.

Ltac inv_evar_begin arg_m ev mm mm' :=
  let e := fresh "expr" in
  let em := fresh "expr_match" in
  match goal with [h: eval_expr _ ?env arg_m _ (Evar ?a1 ?a2) _ ?m' _ |- ?c] =>
    pose (e := Evar a1 a2); 
    pose (ev:=env); pose (mm:=arg_m); pose (mm':=m');
    assert
      (em: match e with
                   |Evar a b => 
                     (a=a1)/\(b=a2)/\(env=ev)/\(arg_m=mm)/\(m'=mm')
                   |_ => False
                 end)
      by repeat (split||reflexivity);
  fold e in h;
  revert em;
  case_h h;
  clear e
  end.
  
Ltac inv_evar arg_m :=
  let ev:=fresh "ev" in 
  let mm:=fresh "mm" in 
  let mm':=fresh "mm'" in
  inv_evar_begin arg_m ev mm mm';
  intros e0 m1 x ty;
  inv_end ev mm mm'. 

Ltac inv_evalof_simplrv_begin v :=
  match goal with [h: eval_simple_rvalue _ _ _ (Evalof ?a1 ?a2) v |- ?c] =>
    let e := fresh "expr" in
    pose (e := Evalof a1 a2);
    assert
      (rm: match e with
                   |Evalof a b =>(a = a1) /\ (b = a2)
                   |_=>False
                 end)
      by repeat  (split||reflexivity);
    fold e in h;
    revert rm;
    case_h h;
    clear e
  end.

Ltac inv_evalof_simplrv_end :=
   let ae := fresh "ae" in (intro ae; and_eq_subst ae).

Ltac inv_evalof_simplrv v b0 ofs v0 H H0 H1 :=
  inv_evalof_simplrv_begin v;
  intros b0 ofs l0 ty v0 H H0 H1;
  inv_evalof_simplrv_end. 

Ltac inv_av_cons_begin arg_m ev :=
  let lst := fresh "lst" in
  match goal with [av: alloc_variables ?env arg_m ((?id,?ty) ::?t) ?a3 ?a4 |- ?c] => 
    pose (lst := ((id,ty)::t)); pose (ev:=env);
    change (alloc_variables ev arg_m lst a3 a4) in av;
    assert
      (lm: match lst with
                    |(a,b)::c=>(a=id)/\(b=ty)/\(c=t)/\(ev=env)
                    |_=>False
                  end)
      by repeat (split||reflexivity);
    revert lm;
    case_h av;
    clear lst
  end.

Ltac inv_av_cons_end ev :=
   unfold ev in *; clear ev; 
   let ae := fresh "ae" in (intro ae; and_eq_subst ae).  

Ltac inv_av_cons arg_m m m1 b1 m4 e2 H H0:=
  let ev:=fresh "ev" in 
  inv_av_cons_begin arg_m ev;
  intros e0 m id0 ty vars m1 b1 m4 e2 H H0;
  inv_av_cons_end ev.

Ltac inv_av_nil_begin arg_m lnil ev ev' :=  
  match goal with [av: alloc_variables ?env arg_m ?lst ?env' ?a4 |- ?c] =>
    pose (lnil:=lst); pose (ev:=env); pose (ev':=env');
    change (alloc_variables ev arg_m lnil ev' a4) in av;
    assert (lm:match lnil with 
                        |nil =>(nil = lst)/\(ev=env)/\(ev'=env')
                        |_ =>False end) 
      by repeat (split||reflexivity);
    revert lm;
    case_h av    
  end.

Ltac inv_av_nil_end lnil ev ev' :=
   unfold lnil, ev, ev' in *; clear lnil ev ev'; 
   let ae := fresh "ae" in (intro ae; and_eq_subst ae).

Ltac inv_av_nil arg_m e0 m :=
  let lnil:=fresh "lnil" in 
  let ev:=fresh "ev" in 
  let ev':=fresh "ev'" in 
  inv_av_nil_begin arg_m lnil ev ev';
  intros e0 m;
  inv_av_nil_end lnil ev ev'.
*)



(* Example lemma to test my_inversion *)

(* Functional relation between the C memory module which contains the other ADC parameters, 
   and the COQ specification of ADC parameters *)
Definition sbit_func_related (m:Mem.mem) (e:env) (sbit:bool):Prop:=
  bit_proj m e S = sbit.

Definition cond_func_related (m:Mem.mem) (e:env) (cond:opcode):Prop:=
  cond_proj m e = cond.

Definition d_func_related (m:Mem.mem) (e:env) (d:regnum):Prop:=
  reg_proj m e adc_compcert.d = d.

Definition n_func_related (m:Mem.mem) (e:env) (n:regnum):Prop:=
  reg_proj m e adc_compcert.n = n.

Definition so_func_related (m:Mem.mem) (e:env) (so:word):Prop:=
  bits_proj m e shifter_operand = so.

(* Human readable renaming of [p], which is generated by the Coq printer *)
Definition prog_adc := adc_compcert.p.

(* Example on Econdition *)
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
  (*
  generalize
    (match H in (eval_expr _ e m _ ex _ m' ex')
       return inv_expr_condition (Genv.globalenv prog_adc) e m ex m' ex' with
       |eval_condition _ _ _ _ _ _ t1 mi a1' v1 t2 _ a' v' b v H1 H2 H3 H4 H5 H6=>
         (fun X k => k t1 mi a1' v1 t2 a' v' b v  H1 H2 H3 H4 H5 H6)
       |_=> I
     end). clear H.
  intro k. red in k. revert H0. apply k. clear k.*)
  inv_condition m m'.
  intros until v0. intros ee1 esr1 bv ee2 esr2 sc esr0.
  inv_binop m m'0. intros until a2'. intros ee11 ee12 esr1.
  inv_valof m m'1. intros until a'1. intros ee11 esr1.
  inv_var m m'1.

  inv_val m m'0. intros ee2 esr.
  destruct b.
    inv_condition m m'. intros until v3. intros ee1 esr1 bv1 ee2 esr2 sc1 esr01.
    inv_binop m m'2. intros until a2'0. intros ee11 ee12 esr1.
    inv_valof m m'3. intros until a'3. intros ee1 esr1.
    inv_var m m'3.
    inv_val m m'2. intros ee1 esr1.
    destruct b.
      inv_val m m'. intros esr3 esr4 esr5.
      reflexivity.
      inv_val m m'. intros esr2 esr3 esr4.
      reflexivity.
    inv_val m m'. intros esr1 esr2.
    reflexivity.
Qed.


(* Example on Ebinop *)
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
(*
  generalize 
    (match H in (eval_expr _ e m _ ex _ m'' ex')
       return inv_expr_binop (Genv.globalenv prog_adc) e m ex m'' ex' with
       |eval_binop _ _ _ t1 m' a1' _ t2 m'' a2' _ _ H1 H2 =>
         (fun X k => k t1 m' a1' t2 a2' H1 H2)
       |_=>I
     end). clear H.
  intro k. red in k. revert H0. apply k. clear k.
  intros until a2'. intros ee1 ee2 esr.
  inv_val m'0 m'.
*)
inv_binop m m'. intros until a2'. intros ee1 ee2 esr.
inv_valof m m'0. intros until a'0. intros ee esr.
inv_val m'0 m'. intros esr.
inv_var m m'0.
reflexivity.
Qed.


(* Example on Eassign *)
Definition reg_id id :=
  Ecall (Evalof (Evar adc_compcert.reg T2) T2)
  (Econs (Evalof (Evar adc_compcert.proc T3) T3)
    (Econs 
      (Evalof (Evar id T4) T4) Enil)) T1.

Definition oldrn_assgnt := 
  Eassign (Evar old_Rn T1) (reg_id n) T1.

(* Assume the assignment of old_Rn has no effect on the part of memory
   where located proc*)

(* Return the memory model which only relates to this ident *)
Parameter of_mem : AST.ident -> Mem.mem -> Mem.mem.

Axiom set_oldrn_ok:
  forall m m' v oldrn_blk ofs,
    store_value_of_type T1 m oldrn_blk ofs v = Some m'->
    of_mem adc_compcert.proc m = of_mem adc_compcert.proc m'.

Axiom get_reg_ok :
  forall e id m t m' r,
    eval_expr (Genv.globalenv prog_adc) e m RV (reg_id id) t m' r ->
    eval_expr (Genv.globalenv prog_adc) e m RV (reg_id id) t m r/\m=m'.

Lemma oldrn_assgnt_ok:
 forall e m l b s t m' v,
  proc_state_related (of_mem adc_compcert.proc m) e (Ok tt (mk_semstate l b s)) ->
  eval_expression (Genv.globalenv prog_adc) e m
    oldrn_assgnt t m' v ->
  proc_state_related (of_mem adc_compcert.proc m') e (Ok tt (mk_semstate l b s)).
Proof.
  intros until v. intros psrel rn_as.
  
  inv rn_as.
  unfold oldrn_assgnt in H.
  inv_assign m m'.
  (*
  generalize
    (match H in (eval_expr _ e m _ ex _ m' ex')
       return inv_expr_assign (Genv.globalenv prog_adc) e m ex m' ex' with
       |eval_assign _ _ _ _ _ t1 m1 l' t2 m2 r' b ofs v v' _ H1 H2 H3 H4 H5 H6 H7=>
         (fun X k => k t1 m1 l' t2 m2 r' b ofs v v' H1 H2 H3 H4 H5 H6 H7)
       |_=>I
     end).
  clear H. intro k. red in k.
  revert H0. apply k. clear k.*)
  intros until v'.
  intros ee1 ee2 esl esr sc svot eqt1 esr0.
  inv_var m m1.
  eapply get_reg_ok in ee2.
  destruct ee2. rewrite<-H0 in *. clear m2 H0.
  eapply set_oldrn_ok in svot.  
  rewrite <- svot. exact psrel.
Qed.

(* Example on Eaddrof Efield *)
Lemma addrof_mem_effect:
  forall e m t m' a' v,
    eval_expr (Genv.globalenv prog_adc) e m RV
    (Eaddrof(Efield(Ederef(Evalof (Evar adc_compcert.proc T3) T3) T6) adc_compcert.cpsr T7) T8) t m' a' ->
    eval_simple_rvalue (Genv.globalenv prog_adc) e m' a' v->
    m = m'.
Proof.
  intros.
  inv_addrof m m'. intros until a'0. intros ee esr.
  inv_field m m'.
  intros until a'1. intros ee esr.
  inv_deref m m'. intros until a'2. intros ee esr.
  inv_valof m m'. intros until a'3. intros ee esr.
  inv_var m m'.
  reflexivity.
Qed.
  

(* Example on Ecall, Evalof, Evar *)

Definition get_rd_bit31 :=
  Ecall (Evalof (Evar get_bit T17) T17)
  (Econs (reg_id d)
    (Econs (Eval (Vint (repr 31)) T9)
      Enil)) T10.

Lemma same_get_reg' :
  forall e m0 m0' vargs m l b s d t m' v,
    alloc_variables empty_env m0 
      (fun_internal_ADC.(fn_params) ++ fun_internal_ADC.(fn_vars)) e m0' ->
    bind_parameters e m0' fun_internal_ADC.(fn_params) vargs m ->
    proc_state_related m e (Ok tt (mk_semstate l b s)) ->
    d_func_related m e d ->
    eval_expression (Genv.globalenv prog_adc) e m get_rd_bit31  t m' v->
    v = Vint ((Arm6_State.reg_content s d) [n31]).
Proof.
  intros until v. intros av bp psrel dfrel get_bit.
  
  inversion get_bit as [env m1 gb t1 m1' gb' v1 gb_expr ev_rv Heqenv Heqm
    Heqexp Heqt Heqm' Heqv]; clear get_bit; subst.

  unfold get_rd_bit31 in gb_expr.


(*  revert ev_rv.
*)

(** new thought *)
(** Using impredicative encoding in inversion tactic *)

(* inversion on eval_expr with Ecall *)
(*inv_call m m'. intros until vres. intros ee eel esr1 esl cf ff tf ef esr0.*)
generalize 
  (match gb_expr in (eval_expr _ e m _ ex _ m' ex')
  return inv_expr_ecall (Genv.globalenv prog_adc) e m ex m' ex' with
     |eval_call _ _ rf rargs ty t1 m1 rf' t2 m2 rargs' vf vargs
                      targs tres fd t3 _ vres H1 H2 H3 H4 H5 H6 H7 H8 =>
       (fun X k => k rf t1 m1 rf' t2 m2 rargs' vf vargs 
      targs tres fd t3 vres H1 H2 H3 H4 H5 H6 H7 H8 )
     |_=> I
   end). clear gb_expr.
intro k. red in k. revert ev_rv. apply k. clear k.
intros until vres. 
intros gb_expr ev_explst ev_rv1 ev_simlst Heqty_gb Heqff Heqtyfd ev_funcall. 
intro ev_rv.
(* inversion on eval_expr with Evalof *)
info
generalize 
  (match gb_expr in (eval_expr _ e m _ ex _ m' ex')
     return inv_expr_valof (Genv.globalenv prog_adc) e m ex m' ex' with
     |eval_valof _ _ a t _ a' ty H1 =>
       (fun X k => k t a' H1)
     |_=> I
   end). clear gb_expr.
intro k. red in k. revert ev_rv1. apply k. clear k.
intros until a'. intros gb_expr. intro ev_rv1.
(* inversion on eval_expr with Evar *)
info
generalize
  (match gb_expr in (eval_expr _ _ m _ ex _ m' ex')
     return inv_expr_var ex ex' m m' with
     |eval_var _ _ _ _ => (fun X k => k)
     |_=> I
   end). clear gb_expr. intro k. red in k.
revert ev_explst. revert ev_rv1.
apply k. clear k.
intro ev_rv1. intro ev_explst.


(** Using impredicative encoding, 
   but without considering the output of expression evaluation *)
(*
generalize 
  (match gb_expr in (eval_expr _ e m _ ex _ m' ex')
  return inv_expr_ecall e m ex m' ex' with
     |eval_call e m rf rargs ty t1 m1 rf' t2 m2 rargs' vf vargs
                      targs tres fd t3 m3 vres H1 H2 H3 H4 H5 H6 H7 H8 =>
       (fun X k => k (Genv.globalenv prog_adc) t1 m1 rf' t2 m2 rargs' vf vargs 
                     targs tres fd t3 vres H1 H2 H3 H4 H5 H6 H7 H8)
     |_=> I
   end). clear gb_expr.
intro k. apply k. clear k.
*)

(** Without impredicative encoding *)
(* info 
  match goal with [h : eval_expr _ ?env ?m _ (Ecall ?a1 ?a2 ?a3) _ ?m' _|- ?cl] =>
    let ex := fresh "expr_call" in
    pose (arg1 := a1);  
    pose (arg2 := a2);  
    pose (arg3 := a3);
    pose (ex := Ecall arg1 arg2 arg3);
    change (match ex with 
                      |Ecall a b c => cl
                      |_=> True
                    end);
    assert (ee : ex = Ecall arg1 arg2 arg3) by reflexivity; 
    revert ee;
    revert av bp psrel dfrel;
  
    change (Ecall a1 a2 a3) with ex in gb_expr;
    case gb_expr; try (intros; exact I); clear gb_expr e m t m' gb';
    intros e m rf rargs ty t1 m1 rf' t2 m2 rargs' vf vargs0 targs tres fd
      t3 m3 vres;
    intros gb_expr ev_exlst ev_simprv1 ev_simplst Heqtyrf Heqff Heqtyfd ev_funcall;
    intros av bp pstrl dfrel Heqexpr ev_simprv;
    injection Heqexpr; intros Heqty Heqrargs Heqrf;
    unfold arg1, arg2, arg3 in Heqty, Heqrargs, Heqrf; 
    clear arg1 arg2 arg3 Heqexpr expr_call;
    rewrite Heqty in ev_simprv;
    rewrite Heqrargs in ev_exlst;
    rewrite Heqrf in gb_expr, Heqtyrf;
    clear Heqty Heqrargs Heqrf
  end.
*)  

(* *********************************************************************)
(** old one *)
(** With extra equalities introduced in inversion tactic *)
(* 
Ltac inv_ecall_begin ev mm mm' :=
  let e := fresh "expr" in
  let em := fresh "expr_match" in
  match goal with [h : eval_expr _ ?env ?m _ (Ecall ?a1 ?a2 ?a3) _ ?m' _|- ?c] =>
    pose (e := Ecall a1 a2 a3); 
    pose (ev:=env); pose (mm:=m); pose (mm':=m');
    assert 
      (em : match e with 
                      |Ecall a b c =>
                        (a=a1)/\(b=a2)/\(c=a3)/\(env=ev)/\(m=mm)/\(m'=mm')
                      |_=> False
                    end)
      by repeat (split || reflexivity);
  fold e in h;
  revert em;
  case_h h;
  clear e
  end.
*)

(*
  inv_ecall m t1 m2 rf' t2 m3 rargs' vf vargs0 targs tres fd t3 vres
            gb_expr explst ev_rv1 ev_simlst H_ Heqfindfd Heqt16 ev_funcall. clear H_.
  intro ev_rv.
*)


(*
  (*harmless inversion: no ordering changes, no new hyp*)
  inversion ev_rv; subst; clear ev_rv.

  revert ev_rv1.
  inv_evalof m t0 m'0 a' H.
(*intro ev_rv1.

  revert ev_rv1.*)
  inv_evar m.
  intro ev_rv1.
  clear t0 a'.

  inv_evalof_simplrv vf b0 ofs v0 ev_simpl_lv Heqty Heqlvot.

  assert (globenv: e!get_bit=None).
    simpl in av.
    
    inv_av_cons m0 ma_proc m_proc b_proc m_proc' e_proc Heqma_proc av.
    inv_av_cons m_proc ma_s m_s b_s m_s' e_s Heqma_s av.
    inv_av_cons m_s ma_cond m_cond b_cond m_cond' e_cond Heqma_cond av.
    inv_av_cons m_cond ma_d m_d b_d m_d' e_d Heqma_d av.
    inv_av_cons m_d ma_n m_n b_n m_n' e_n Heqma_n av.
    inv_av_cons m_n ma_so m_so b_so m_so' e_so Heqma_so av.
    inv_av_cons m_so ma_on m_on b_on m_on' e_on Heqma_on av.

    inv_av_nil_begin m_on lnil ev ev'.
    intros.

    destruct lm as [feq ae]; clear feq.
    destruct ae as [feq ae]; rewrite feq in *; clear feq.
    rewrite <- ae in *; clear ae.

    
*)
    (*
    simpl; reflexivity.

  match goal with [_: eval_simple_lvalue _ _ _ (Evar ?a1 ?a2) _ _ |- ?c] =>
    assert
      (lv_match: match expr_evar with
                   |Evar a b =>(a = a1) /\ (b = a2)
                   |_=>False
                 end)
      by repeat  (split||reflexivity)
  end. 
  fold expr_evar in ev_lv.
  revert lv_match.

  case_h ev_lv.
    (*get_bit is in global environment *)
    intros until b1. intro locenv. intros.
    destruct lv_match as [eq1 eq2]; subst.
    rewrite locenv in globenv; discriminate.
    (*get_bit is in local environment *)
    intros until b1; intros _ Heqfindsymb _; intros.
    destruct lv_match as [eq1 eq2]; rewrite eq1 in *; clear eq1 eq2.*)

    (*match goal with [_:eval_exprlist _ _ _ (Econs ?a1 ?a2) _ _ _]*)
    
    
   
  

(* useful trick for later
  match goal with [_ : eval_expr _ _ _ _ ?interesting _ _ _ |- ?c ] => 
     let name := fresh e0 in 
     pose (name := interesting) end.
*)  

  (*revert gb_sim_rv.  
  generalize (refl_equal get_bit_reg).
  unfold get_bit_reg at 2.
  case gb_expr; clear gb_expr; try (intros; discriminate). 
  intros. injection H7. clear H7. intros; subst.*)


(*match goal with [ |- context c [Ecall ?a1 ?a2 ?a3]] => pattern a1, a2, a3 end.
    change 
      (match Ecall (Evalof (Evar get_bit T16) T16)
     (Econs (reg_id adc_compcert.d)
        (Econs (Eval (Vint (repr 31)) T9) Enil)) T4 with 
         | Ecall a b c => 
(fun (e0 : expr) (e1 : exprlist) (t0 : type) =>
    get_bit_reg = Ecall e0 e1 t0 ->
    v = Vint (Arm6_State.reg_content s d) [n31]) a b c
 | _ => True end). cbv beta.
  case_I gb_expr. red.
*)

(*
  generalize (refl_equal get_bit_reg).
  pattern get_bit_reg at 1.*)

  (*match goal with [ |- ?concl _ _ _ ] =>
    change 
      (match Ecall a1 a2 a3 with 
         | Ecall a b c => concl a b c | _ => True end) end. cbv beta.
  
  unfold get_bit_reg in gb_expr.
match goal with [ |- ?concl] => change ((fun _ _ _ => concl) 
   (Evalof (Evar get_bit T16) T16)
   (Econs (reg_id adc_compcert.d)
                    (Econs (Eval (Vint (repr 31)) T9) Enil))
   T4) end.
  match goal with [ gb_expr : context c [Ecall ?a1 ?a2 ?a3] |- ?concl _ _ _ ] =>
    change 
      (match Ecall a1 a2 a3 with 
         | Ecall a b c => concl a b c | _ => True end) end. cbv beta.
  case_I gb_expr. red.
  intros until rargs. intro ty.
  intros until vres.
  intros rf_exp rargs_exp vf_rval targs_vlst Heqtprf Heqfun Heqtpfun fd_funcall.
  
  match goal with [ |- ?concl _ _ _ ] =>
    change 
      (match get_bit_reg with 
         | Ecall a b c => concl a b c | _ => True end) end. cbv beta.
  

  case_eq get_bit_reg. intro
  case get_bit. intro
  unfold get_bit_reg in get_bit.*)

Admitted.