Require Import Csyntax Csem Cstrategy Coqlib Integers Values Maps Errors. 


(* The assignment of old_Rn has a normal outcome *)
Lemma normal_outcome_for_assgnt: 
  forall a1 a2 ge t ev m e m' out,
  exec_stmt ge e m (Sdo (Eassign a1 a2 t)) ev m' out ->
  out = Out_normal.
Proof.
intros until out. intros exst. 
inv exst. reflexivity.
Qed.

Implicit Arguments normal_outcome_for_assgnt [a1 a2 ge t ev m e m' out].

Ltac noa :=
  match goal with
    [He: exec_stmt _ _ _ (Sdo (Eassign _ _ _)) _ _ ?out,
     Hd: ?out <> Out_normal |- _ ] =>
       case Hd; 
       apply (normal_outcome_for_assgnt He) end.

(* Any Sdo has a normal outcome*)
Lemma normal_outcome_for_do:
  forall exp ge t m e m' out,
    exec_stmt ge e m (Sdo exp) t m' out ->
    out = Out_normal.
Proof.
  intros until out. intros exst.
  inv exst. reflexivity.
Qed.

Implicit Arguments normal_outcome_for_do [exp ge t m e m' out].

Ltac nod :=
  match goal with
    [He: exec_stmt _ _ _ (Sdo _) _ _ ?out,
     Hd: ?out <> Out_normal |- _ ] =>
       case Hd; 
       apply (normal_outcome_for_do He) end.  
