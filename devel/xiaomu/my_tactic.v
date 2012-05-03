Require Import Csyntax Csem Cstrategy Coqlib Integers Values Maps Errors Memory Globalenvs.


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

Lemma alloc_diff_block :
  forall m e e' m' x y b_x tx b_y ty,
    alloc_variables e m ((x,tx)::(y,ty)::nil) e' m'->
    list_norepet (x::y::nil) ->
    e' ! x = Some (b_x, tx) ->
    e' ! y = Some (b_y, ty) ->
    b_x <> b_y.
Proof.
  intros until ty. intros av norepet getx gety.
  inv av. inv H7. inv H9.
  apply Mem.valid_new_block in H6.
  unfold Mem.valid_block in H6.
  apply Mem.alloc_result in H8.
  rewrite <- H8 in H6; clear H8.
(* SearchPattern (_ < _ -> _ <> _). *)
  apply Zlt_not_eq in H6.
  assert (findy: (PTree.set y (b0, ty) (PTree.set x (b1, tx) e)) ! y =
                  Some (b0, ty)).
  apply PTree.gss. rewrite findy in gety. inversion gety.

  assert (findx: (PTree.set y (b0, ty) (PTree.set x (b1, tx) e)) ! x =
                  (PTree.set x (b1, tx) e) ! x).
  apply PTree.gso.
  inv norepet. unfold In in H2. intro exy. apply H2. left. symmetry. exact exy.

(*info intuition.*)

  rewrite findx in getx.
  rewrite PTree.gss in getx. inversion getx.
  rewrite <- H0. rewrite <- H1.
  exact H6.
Qed.

Lemma lt_block :
  forall m1 ofs1 b1 m2 ofs2 b2 m3,
    Mem.alloc m1 0 ofs1 = (m2, b1) ->
    Mem.alloc m2 0 ofs2 = (m3, b2) ->
    b1 < b2.
Proof.
  intros until m3. intros alc1 alc2.
  apply Mem.valid_new_block in alc1. unfold Mem.valid_block in alc1.
  apply Mem.alloc_result in alc2. rewrite <- alc2 in alc1.
  exact alc1.
Qed.


Ltac blocks_lt b1 b2 :=
  match goal with [alc1: Mem.alloc ?m1 ?l1 ?h1 = (?m2, b1) |- ?c1 ]=>
    match goal with
      |[alc2: Mem.alloc m2 ?l2 ?h2 = (?m3, b2) |- ?c ] =>
        apply lt_block with m1 h1 b1 m2 h2 b2 m3 in alc1;
          [idtac|exact alc2]
      |[alc2: Mem.alloc ?mx ?lx ?hx = (?my, ?bx) |- ?c ] =>
        apply lt_block with m1 h1 b1 mx hx bx my in alc1;
          [blocks_lt bx b2|exact alc2]
    end
  end.

Ltac blocks_lt' b1 b2 :=
  match goal with
    |[lt1: b1 < b2 |- ?c] => idtac
    |[lt1: b1 < ?bx |- ?c] =>
      match goal with
        |[lt2: bx < b2 |- ?c] => 
          apply (Zlt_trans b1) in lt2;
            [clear lt1|exact lt1]
        |[lt2: bx <?bxx |-?c]=>
          try apply (Zlt_trans b1) in lt2;
            [clear lt1;blocks_lt' b1 b2|exact lt1]
      end
  end.

Ltac blocks_neq b1 b2 :=
  match goal with
    |[lt1: b1 < b2 |- ?c] => apply Zlt_not_eq in lt1
    |[lt1: b1 < ?bx |- ?c] =>
      match goal with
        |[lt2: bx < b2 |- ?c] => 
          apply (Zlt_trans b1) in lt2;
            [clear lt1;apply Zlt_not_eq in lt2|exact lt1]
        |[lt2: bx <?bxx |-?c]=>
          try apply (Zlt_trans b1) in lt2;
            [clear lt1;blocks_neq b1 b2|exact lt1]
      end
  end.

Ltac diff_blk b1 b2:=
  blocks_lt b1 b2; blocks_neq b1 b2.

Lemma diff_block :
  forall m1 ofs1 b1 m2 ofs2 b2 m3,
    Mem.alloc m1 0 ofs1 = (m2, b1) ->
    Mem.alloc m2 0 ofs2 = (m3, b2) ->
    b1 <> b2.
Proof.
  intros until m3. intros alc1 alc2.
  apply Mem.valid_new_block in alc1. unfold Mem.valid_block in alc1.
  apply Mem.alloc_result in alc2. rewrite <- alc2 in alc1.
  apply Zlt_not_eq in alc1.
  exact alc1.
Qed.

Ltac rrw_block :=
  let Heq := fresh "Heq" in
  match goal with [eq:Some ?l = Some (?b,?t)|-?c] => 
    injection eq;intro Heq;rewrite<-Heq in *;clear Heq eq b end.

(* The loaded value from block b is not changed between m1, m2.
   From m1 to m2, we consider all the storage in memory. 
   If there is no store on block b, then the value in b is not changed *)
Ltac val_not_changed_str ck b o m m' :=
  match goal with
    |[str1: Mem.store ?ck1 m b ?ofs1 ?v1 = Some ?m2 |-?c]=>idtac
    |[str1: Mem.store ?ck1 m ?b1 ?ofs1 ?v1 = Some m' |-?c]=>
      generalize str1;
      apply Mem.load_store_other with ck1 m b1 ofs1 v1 m' ck b o in str1;
        [idtac|left;diff_blk b b1;assumption]
    |[str1: Mem.store ?ck1 m ?b1 ?ofs1 ?v1 = Some ?m2 |-?c]=>
      match goal with
        |[str2: Mem.store ?ck2 m2 ?b2 ?ofs2 ?v2 = Some ?m3|-?c]=>
          generalize str1;
          apply Mem.load_store_other with ck1 m b1 ofs1 v1 m2 ck b o in str1;
            [idtac|left;diff_blk b b1;assumption];
          val_not_changed_str ck b o m2 m'
      end
  end.

Ltac find_func :=
  match goal with 
    [fs:context [Genv.find_symbol],
      l:context [load_value_of_type],
      ff:context [Genv.find_funct]|-?cl]=>
    unfold Genv.find_symbol in fs;simpl in fs;
    injection fs;intro Heqfs;subst;clear fs;
        
    unfold load_value_of_type in l;simpl in l;
    injection l;intro Heql;subst;clear l;

    erewrite Genv.find_funct_find_funct_ptr in ff;
    unfold Genv.find_funct_ptr in ff;unfold ZMap.get in ff;simpl in ff;
    unfold ZMap.set in ff;simpl in ff;
    repeat (rewrite PMap.gso in ff;[idtac|simpl;congruence]);
    rewrite PMap.gss in ff;
    injection ff;intro Heqf;subst;clear ff        
  end.