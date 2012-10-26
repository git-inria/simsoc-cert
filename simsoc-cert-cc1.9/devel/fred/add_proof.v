(**
SimSoC-Cert, a toolkit for generating certified processor simulators
See the COPYRIGHTS and LICENSE files.

Proof of add.
*)

Set Implicit Arguments.

Require Import Csem Cstrategy Smallstep Events Integers Globalenvs AST Memory
  Csyntax Coqlib Maps.

Fixpoint alloc_variables_fun e m l :=
  match l with
    | nil => (e, m)
    | (id, ty) :: vars =>
      let (m1, b1) := Mem.alloc m 0 (sizeof ty) in
        alloc_variables_fun (PTree.set id (b1, ty) e) m1 vars
  end.

Lemma alloc_variables_fun_ok : forall l e m e' m',
  alloc_variables_fun e m l = (e', m') -> alloc_variables e m l e' m'.

Proof.
induction l; simpl; intros.
inversion H. apply alloc_variables_nil.
destruct a as [id ty]. generalize H; clear H.
case_eq (Mem.alloc m 0 (sizeof ty)). intros m1 b1 h1 h2.
eapply alloc_variables_cons. apply h1. apply IHl. auto.
Qed.

Variable beq_type : type -> type -> bool.
Variable beq_type_ok : forall t u, beq_type t u = true <-> t = u.

Fixpoint bind_parameters_fun e m (l1 : list (ident * type)) l2 :=
  match l1, l2 with
    | nil, nil => Some m
    | (id, ty) :: params, v1 :: vl =>
      match PTree.get id e with
        | Some (b, ty') =>
          if beq_type ty ty' then
            match store_value_of_type ty m b Int.zero v1 with
              | Some m1 => bind_parameters_fun e m1 params vl
              | _ => None
            end
          else None
        | _ => None
      end
    | _, _ => None
  end.

Lemma bind_parameters_fun_ok : forall l1 l2 e m m2,
  bind_parameters_fun e m l1 l2 = Some m2 -> bind_parameters e m l1 l2 m2.

Proof.
induction l1; destruct l2; simpl; intros e m m2 h.
inversion h. apply bind_parameters_nil.
discriminate.
destruct a. discriminate.
destruct a.
generalize h; clear h. case_eq (e!i). 2: intros; discriminate.
intros [b ty] h1. case_eq (beq_type t ty). 2: intros; discriminate.
rewrite beq_type_ok. intro. subst.
case_eq (store_value_of_type ty m b Int.zero v). 2: intros; discriminate.
intros m1 h2 h. eapply bind_parameters_cons.
apply h1. apply h2. apply IHl1. auto.
Qed.

Lemma step_internal_function': forall ge f vargs k m e m1 m2,
  list_norepet (var_names f.(fn_params) ++ var_names f.(fn_vars)) ->
  alloc_variables_fun empty_env m (f.(fn_params) ++ f.(fn_vars)) = (e, m1) ->
  bind_parameters_fun e m1 f.(fn_params) vargs = Some m2 ->
  sstep ge (Callstate (Internal f) vargs k m) E0
  (Csem.State f f.(fn_body) k e m2).

Proof.
intros. eapply step_internal_function. auto.
apply alloc_variables_fun_ok. apply H0.
apply bind_parameters_fun_ok. auto.
Qed.

Require Import Util Cnotations add.

Open Scope positive_scope.

Ltac norm e := let x := fresh in set (x := e); vm_compute in x; subst x.

Ltac comp :=
  match goal with
    | |- ?l = _ => norm l
    | |- Csem.alloc_variables _ _ ?l _ _ => norm l
    | |- Csem.bind_parameters _ _ ?l _ _ => norm l
  end.

Ltac hnorm e := let x := fresh in set (x := e); hnf in x; subst x.

Ltac hcomp :=
  match goal with
    | |- ?l = _ => hnorm l
    | |- Csem.alloc_variables _ _ ?l _ _ => hnorm l
    | |- Csem.bind_parameters _ _ ?l _ _ => hnorm l
  end.

Ltac alloc :=
  match goal with
    | |- Csem.alloc_variables _ _ nil _ _ => simple apply alloc_variables_nil
    | |- Csem.alloc_variables _ _ (cons _ _) _ _ =>
      simple eapply alloc_variables_cons; [comp; refl | alloc]
  end.

Ltac bind :=
  match goal with
    | |- Csem.bind_parameters _ _ nil _ _ => simple apply bind_parameters_nil
    | |- Csem.bind_parameters _ _ (cons _ _) _ _ =>
      simple eapply bind_parameters_cons; [hcomp; refl | bind]
  end.

Ltac s := simple eapply star_step with (t:=E0)(t1:=E0)(t2:=E0);
  [right|idtac|refl].

Ltac e := simple eapply star_step with (t:=E0)(t1:=E0)(t2:=E0);
  [left |idtac|refl].

Set Printing Depth 11.

Lemma add_ok : exists t, exists k, exec_program p (Terminates t k).

Proof.
simple eapply ex_intro. simple eapply ex_intro.
unfold exec_program. simple eapply program_terminates.

(* final state *)
3: simple apply final_state_intro.

(* initial state *)
simple eapply initial_state_intro.
comp; refl.
comp; refl.
comp; refl.
refl.

(* steps *)
s. simple eapply step_internal_function.
list_norepet beq_positive_ok.
comp; alloc.
comp; bind.
(*comp. refl.
hcomp. refl.*)

(* x = 2 *)
s. apply step_seq.
s. simple apply step_do_1.

e. simple eapply step_assign with (C:=fun x =>x).
simple apply lctx_top.
simple apply esl_var_local. comp; refl.
simple apply esr_val.
simpl typeof. simple apply cast_nn_i; simple apply nfc_int.
comp; refl.
refl.

s. simple apply step_do_2.
s. simple apply step_skip_seq.

(* y = 3 *)
s. simple apply step_seq.
s. simple apply step_do_1.

e. simple eapply step_assign with (C:=fun x =>x).
simple apply lctx_top.
simple apply esl_var_local. comp; refl.
simple apply esr_val.
simpl typeof. simple apply cast_nn_i; simple apply nfc_int.
comp; refl.
refl.

s. simple apply step_do_2.
s. simple apply step_skip_seq.

(* return x + y *)
s. simple apply step_return_1.
e. simple apply step_expr.
simple eapply esr_binop.
simple eapply esr_rvalof.
simple apply esl_var_local. comp; refl.
refl.
comp. refl.
simple eapply esr_rvalof.
simple apply esl_var_local. comp; refl.
refl.
comp; refl.
