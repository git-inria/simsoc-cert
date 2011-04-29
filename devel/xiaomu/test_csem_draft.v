Require Import AST Coqlib Integers Maps Values.

Require Import Axioms.
Require Import Floats.
Require Export Memdata.
Require Export Memtype.

Definition update (A: Type) (x: Z) (v: A) (f: Z -> A) : Z -> A :=
  fun y => if zeq y x then v else f y.

Implicit Arguments update [A].

Lemma update_s:
  forall (A: Type) (x: Z) (v: A) (f: Z -> A),
  update x v f x = v.
Proof.
  intros; unfold update. apply zeq_true.
Qed.

Lemma update_o:
  forall (A: Type) (x: Z) (v: A) (f: Z -> A) (y: Z),
  x <> y -> update x v f y = f y.
Proof.
  intros; unfold update. apply zeq_false; auto.
Qed.

Module Mem <: MEM.

Definition perm_order' (po: option permission) (p: permission) := 
  match po with
  | Some p' => perm_order p' p
  | None => False
 end.

Record mem' : Type := mkmem {
  mem_contents: block -> Z -> memval;
  mem_access: block -> Z -> option permission;
  bounds: block -> Z * Z;
  nextblock: block;
  nextblock_pos: nextblock > 0;
  nextblock_noaccess: forall b, 0 < b < nextblock \/ bounds b = (0,0) ;
  bounds_noaccess: forall b ofs, ofs < fst(bounds b) \/ ofs >= snd(bounds b) -> mem_access b ofs = None;
  noread_undef: forall b ofs,  perm_order' (mem_access b ofs) Readable \/ mem_contents b ofs = Undef
}.

Definition mem := mem'.

Lemma mkmem_ext:
 forall cont1 cont2 acc1 acc2 bound1 bound2 next1 next2 
          a1 a2 b1 b2 c1 c2 d1 d2,
  cont1=cont2 -> acc1=acc2 -> bound1=bound2 -> next1=next2 ->
  mkmem cont1 acc1 bound1 next1 a1 b1 c1 d1 =
  mkmem cont2 acc2 bound2 next2 a2 b2 c2 d2.
Proof.
  intros. subst. f_equal; apply proof_irr.
Qed.

(** * Validity of blocks and accesses *)

(** A block address is valid if it was previously allocated. It remains valid
  even after being freed. *)

Definition valid_block (m: mem) (b: block) :=
  b < nextblock m.

Theorem valid_not_valid_diff:
  forall m b b', valid_block m b -> ~(valid_block m b') -> b <> b'.
Proof.
  intros; red; intros. subst b'. contradiction.
Qed.

Hint Local Resolve valid_not_valid_diff: mem.

(** Permissions *)

Definition perm (m: mem) (b: block) (ofs: Z) (p: permission) : Prop :=
   perm_order' (mem_access m b ofs) p.

Theorem perm_implies:
  forall m b ofs p1 p2, perm m b ofs p1 -> perm_order p1 p2 -> perm m b ofs p2.
Proof.
  unfold perm, perm_order'; intros.
  destruct (mem_access m b ofs); auto.
  eapply perm_order_trans; eauto.
Qed.

Hint Local Resolve perm_implies: mem.

Theorem perm_valid_block:
  forall m b ofs p, perm m b ofs p -> valid_block m b.
Proof.
  unfold perm; intros. 
  destruct (zlt b m.(nextblock)).
  auto.
  assert (mem_access m b ofs = None). 
  destruct (nextblock_noaccess m b).
  elimtype False; omega.
  apply bounds_noaccess. rewrite H0; simpl; omega.
  rewrite H0 in H.
  contradiction.
Qed.

Hint Local Resolve perm_valid_block: mem.

Remark perm_order_dec:
  forall p1 p2, {perm_order p1 p2} + {~perm_order p1 p2}.
Proof.
  intros. destruct p1; destruct p2; (left; constructor) || (right; intro PO; inversion PO).
Qed.

Remark perm_order'_dec:
  forall op p, {perm_order' op p} + {~perm_order' op p}.
Proof.
  intros. destruct op; unfold perm_order'.
  apply perm_order_dec.
  right; tauto.
Qed.

Theorem perm_dec:
  forall m b ofs p, {perm m b ofs p} + {~ perm m b ofs p}.
Proof.
  unfold perm; intros.
  apply perm_order'_dec.
Qed.
 
Definition range_perm (m: mem) (b: block) (lo hi: Z) (p: permission) : Prop :=
  forall ofs, lo <= ofs < hi -> perm m b ofs p.

Theorem range_perm_implies:
  forall m b lo hi p1 p2,
  range_perm m b lo hi p1 -> perm_order p1 p2 -> range_perm m b lo hi p2.
Proof.
  unfold range_perm; intros; eauto with mem.
Qed.

Hint Local Resolve range_perm_implies: mem.

Lemma range_perm_dec:
  forall m b lo hi p, {range_perm m b lo hi p} + {~ range_perm m b lo hi p}.
Proof.
  intros. 
  assert (forall n, 0 <= n ->
          {range_perm m b lo (lo + n) p} + {~ range_perm m b lo (lo + n) p}).
    apply natlike_rec2.
    left. red; intros. omegaContradiction.
    intros. destruct H0. 
    destruct (perm_dec m b (lo + z) p). 
    left. red; intros. destruct (zeq ofs (lo + z)). congruence. apply r. omega. 
    right; red; intro. elim n. apply H0. omega. 
    right; red; intro. elim n. red; intros. apply H0. omega. 
  destruct (zlt lo hi).
  replace hi with (lo + (hi - lo)) by omega. apply H. omega.
  left; red; intros. omegaContradiction. 
Defined.

(** [valid_access m chunk b ofs p] holds if a memory access
    of the given chunk is possible in [m] at address [b, ofs]
    with permissions [p].
    This means:
- The range of bytes accessed all have permission [p].
- The offset [ofs] is aligned.
*)

Definition valid_access (m: mem) (chunk: memory_chunk) (b: block) (ofs: Z) (p: permission): Prop :=
  range_perm m b ofs (ofs + size_chunk chunk) p
  /\ (align_chunk chunk | ofs).

Theorem valid_access_implies:
  forall m chunk b ofs p1 p2,
  valid_access m chunk b ofs p1 -> perm_order p1 p2 ->
  valid_access m chunk b ofs p2.
Proof.
  intros. inv H. constructor; eauto with mem.
Qed.

Theorem valid_access_freeable_any:
  forall m chunk b ofs p,
  valid_access m chunk b ofs Freeable ->
  valid_access m chunk b ofs p.
Proof.
  intros.
  eapply valid_access_implies; eauto. constructor.
Qed.

Hint Local Resolve valid_access_implies: mem.

Theorem valid_access_valid_block:
  forall m chunk b ofs,
  valid_access m chunk b ofs Nonempty ->
  valid_block m b.
Proof.
  intros. destruct H.
  assert (perm m b ofs Nonempty).
    apply H. generalize (size_chunk_pos chunk). omega.
  eauto with mem.
Qed.

Hint Local Resolve valid_access_valid_block: mem.

Lemma valid_access_perm:
  forall m chunk b ofs p,
  valid_access m chunk b ofs p ->
  perm m b ofs p.
Proof.
  intros. destruct H. apply H. generalize (size_chunk_pos chunk). omega.
Qed.

Lemma valid_access_compat:
  forall m chunk1 chunk2 b ofs p,
  size_chunk chunk1 = size_chunk chunk2 ->
  valid_access m chunk1 b ofs p->
  valid_access m chunk2 b ofs p.
Proof.
  intros. inv H0. rewrite H in H1. constructor; auto.
  rewrite <- (align_chunk_compat _ _ H). auto.
Qed.

Lemma valid_access_dec:
  forall m chunk b ofs p,
  {valid_access m chunk b ofs p} + {~ valid_access m chunk b ofs p}.
Proof.
  intros. 
  destruct (range_perm_dec m b ofs (ofs + size_chunk chunk) p).
  destruct (Zdivide_dec (align_chunk chunk) ofs (align_chunk_pos chunk)).
  left; constructor; auto.
  right; red; intro V; inv V; contradiction.
  right; red; intro V; inv V; contradiction.
Defined.

(** [valid_pointer] is a boolean-valued function that says whether
    the byte at the given location is nonempty. *)

Definition valid_pointer (m: mem) (b: block) (ofs: Z): bool :=
  perm_dec m b ofs Nonempty.

Theorem valid_pointer_nonempty_perm:
  forall m b ofs,
  valid_pointer m b ofs = true <-> perm m b ofs Nonempty.
Proof.
  intros. unfold valid_pointer. 
  destruct (perm_dec m b ofs Nonempty); simpl;
  intuition congruence.
Qed.

Theorem valid_pointer_valid_access:
  forall m b ofs,
  valid_pointer m b ofs = true <-> valid_access m Mint8unsigned b ofs Nonempty.
Proof.
  intros. rewrite valid_pointer_nonempty_perm. 
  split; intros.
  split. simpl; red; intros. replace ofs0 with ofs by omega. auto.
  simpl. apply Zone_divide. 
  destruct H. apply H. simpl. omega.
Qed.

(** Bounds *)

(** Each block has a low bound and a high bound, determined at allocation time
    and invariant afterward.  The crucial properties of bounds is
    that any offset below the low bound or above the high bound is
    empty. *)

Notation low_bound m b := (fst(bounds m b)).
Notation high_bound m b := (snd(bounds m b)).

Theorem perm_in_bounds:
  forall m b ofs p, perm m b ofs p -> low_bound m b <= ofs < high_bound m b.
Proof.
  unfold perm. intros.
  destruct (zlt ofs (fst (bounds m b))).
  exploit bounds_noaccess. left; eauto.
  intros.
  rewrite H0 in H. contradiction.
  destruct (zlt ofs (snd (bounds m b))).
  omega. 
  exploit bounds_noaccess. right; eauto.
  intro; rewrite H0 in H. contradiction.
Qed.

Theorem range_perm_in_bounds:
  forall m b lo hi p, 
  range_perm m b lo hi p -> lo < hi -> low_bound m b <= lo /\ hi <= high_bound m b.
Proof.
  intros. split. 
  exploit (perm_in_bounds m b lo p). apply H. omega. omega.
  exploit (perm_in_bounds m b (hi-1) p). apply H. omega. omega.
Qed.

Theorem valid_access_in_bounds:
  forall m chunk b ofs p,
  valid_access m chunk b ofs p ->
  low_bound m b <= ofs /\ ofs + size_chunk chunk <= high_bound m b.
Proof.
  intros. inv H. apply range_perm_in_bounds with p; auto.
  generalize (size_chunk_pos chunk). omega.
Qed.

Hint Local Resolve perm_in_bounds range_perm_in_bounds valid_access_in_bounds.

(** * Store operations *)

(** The initial store *)

Program Definition empty: mem :=
  mkmem (fun b ofs => Undef)
        (fun b ofs => None)
        (fun b => (0,0))
        1 _ _ _ _.
Next Obligation.
  omega.
Qed.

Definition nullptr: block := 0.

(** Allocation of a fresh block with the given bounds.  Return an updated
  memory state and the address of the fresh block, which initially contains
  undefined cells.  Note that allocation never fails: we model an
  infinite memory. *)

Program Definition alloc (m: mem) (lo hi: Z) :=
  (mkmem (update m.(nextblock) 
                 (fun ofs => Undef)
                 m.(mem_contents))
         (update m.(nextblock)
                 (fun ofs => if zle lo ofs && zlt ofs hi then Some Freeable else None)
                 m.(mem_access))
         (update m.(nextblock) (lo, hi) m.(bounds))
         (Zsucc m.(nextblock))
         _ _ _ _,
   m.(nextblock)).
Next Obligation.
  generalize (nextblock_pos m). omega. 
Qed.
Next Obligation.
  assert (0 < b < Zsucc (nextblock m) \/ b <= 0 \/ b > nextblock m) by omega.
  destruct H as [?|[?|?]]. left; omega.
  right.
  rewrite update_o.
  destruct (nextblock_noaccess m b); auto. elimtype False; omega.
  generalize (nextblock_pos m); omega.
(*  generalize (bounds_noaccess m b 0).*)
  destruct (nextblock_noaccess m b); auto. left; omega.
  rewrite update_o. right; auto. omega.
Qed.
Next Obligation.
  unfold update in *. destruct (zeq b (nextblock m)). 
  simpl in H. destruct H. 
  unfold proj_sumbool. rewrite zle_false. auto. omega.
  unfold proj_sumbool. rewrite zlt_false; auto. rewrite andb_false_r. auto.
  apply bounds_noaccess. auto.
Qed.
Next Obligation.
unfold update.
destruct (zeq b (nextblock m)); auto.
apply noread_undef.
Qed.


(** Freeing a block between the given bounds.
  Return the updated memory state where the given range of the given block
  has been invalidated: future reads and writes to this
  range will fail.  Requires write permission on the given range. *)

Definition clearN (m: block -> Z -> memval) (b: block) (lo hi: Z) : 
    block -> Z -> memval :=
   fun b' ofs => if zeq b' b 
                         then if zle lo ofs && zlt ofs hi then Undef else m b' ofs
                         else m b' ofs.

Lemma clearN_in:
   forall m b lo hi ofs, lo <= ofs < hi -> clearN m b lo hi b ofs = Undef.
Proof.
intros. unfold clearN. rewrite zeq_true.
destruct H; unfold andb, proj_sumbool.
rewrite zle_true; auto. rewrite zlt_true; auto.
Qed.

Lemma clearN_out:
  forall m b lo hi b' ofs, (b<>b' \/ ofs < lo \/ hi <= ofs) -> clearN m b lo hi b' ofs = m b' ofs.
Proof.
intros. unfold clearN. destruct (zeq b' b); auto.
subst b'.
destruct H. contradiction H; auto.
destruct (zle lo ofs); auto.
destruct (zlt ofs hi); auto.
elimtype False; omega.
Qed.


Program Definition unchecked_free (m: mem) (b: block) (lo hi: Z): mem :=
  mkmem (clearN m.(mem_contents) b lo hi)
        (update b 
                (fun ofs => if zle lo ofs && zlt ofs hi then None else m.(mem_access) b ofs)
                m.(mem_access))
        m.(bounds)
        m.(nextblock) _ _ _ _.
Next Obligation.
  apply nextblock_pos. 
Qed.
Next Obligation.
apply (nextblock_noaccess m b0).
Qed.
Next Obligation.
  unfold update. destruct (zeq b0 b). subst b0. 
  destruct (zle lo ofs); simpl; auto.
  destruct (zlt ofs hi); simpl; auto.
  apply bounds_noaccess; auto.
  apply bounds_noaccess; auto.
  apply bounds_noaccess; auto.
Qed.
Next Obligation.
  unfold clearN, update.
  destruct (zeq b0 b). subst b0. 
  destruct (zle lo ofs); simpl; auto.
  destruct (zlt ofs hi); simpl; auto.
  apply noread_undef.
  apply noread_undef.
  apply noread_undef.
Qed.

Definition free (m: mem) (b: block) (lo hi: Z): option mem :=
  if range_perm_dec m b lo hi Freeable 
  then Some(unchecked_free m b lo hi)
  else None.

Fixpoint free_list (m: mem) (l: list (block * Z * Z)) {struct l}: option mem :=
  match l with
  | nil => Some m
  | (b, lo, hi) :: l' =>
      match free m b lo hi with
      | None => None
      | Some m' => free_list m' l'
      end
  end.

(** Memory reads. *)

(** Reading N adjacent bytes in a block content. *)

Fixpoint getN (n: nat) (p: Z) (c: Z -> memval) {struct n}: list memval :=
  match n with
  | O => nil
  | S n' => c p :: getN n' (p + 1) c
  end.

(** [load chunk m b ofs] perform a read in memory state [m], at address
  [b] and offset [ofs].  It returns the value of the memory chunk
  at that address.  [None] is returned if the accessed bytes
  are not readable. *)

Definition load (chunk: memory_chunk) (m: mem) (b: block) (ofs: Z): option val :=
  if valid_access_dec m chunk b ofs Readable
  then Some(decode_val chunk (getN (size_chunk_nat chunk) ofs (m.(mem_contents) b)))
  else None.

(** [loadv chunk m addr] is similar, but the address and offset are given
  as a single value [addr], which must be a pointer value. *)

Definition loadv (chunk: memory_chunk) (m: mem) (addr: val) : option val :=
  match addr with
  | Vptr b ofs => load chunk m b (Int.signed ofs)
  | _ => None
  end.

(** [loadbytes m b ofs n] reads [n] consecutive bytes starting at
  location [(b, ofs)].  Returns [None] if the accessed locations are
  not readable. *)

Definition loadbytes (m: mem) (b: block) (ofs n: Z): option (list memval) :=
  if range_perm_dec m b ofs (ofs + n) Readable
  then Some (getN (nat_of_Z n) ofs (m.(mem_contents) b))
  else None.

(** Memory stores. *)

(** Writing N adjacent bytes in a block content. *)

Fixpoint setN (vl: list memval) (p: Z) (c: Z -> memval) {struct vl}: Z -> memval :=
  match vl with
  | nil => c
  | v :: vl' => setN vl' (p + 1) (update p v c)
  end.


Remark setN_other:
  forall vl c p q,
  (forall r, p <= r < p + Z_of_nat (length vl) -> r <> q) ->
  setN vl p c q = c q.
Proof.
  induction vl; intros; simpl.
  auto. 
  simpl length in H. rewrite inj_S in H.
  transitivity (update p a c q).
  apply IHvl. intros. apply H. omega. 
  apply update_o. apply H. omega. 
Qed.

Remark setN_outside:
  forall vl c p q,
  q < p \/ q >= p + Z_of_nat (length vl) ->
  setN vl p c q = c q.
Proof.
  intros. apply setN_other. 
  intros. omega. 
Qed.

Remark getN_setN_same:
  forall vl p c,
  getN (length vl) p (setN vl p c) = vl.
Proof.
  induction vl; intros; simpl.
  auto.
  decEq. 
  rewrite setN_outside. apply update_s. omega. 
  apply IHvl. 
Qed.

Remark getN_exten:
  forall c1 c2 n p,
  (forall i, p <= i < p + Z_of_nat n -> c1 i = c2 i) ->
  getN n p c1 = getN n p c2.
Proof.
  induction n; intros. auto. rewrite inj_S in H. simpl. decEq. 
  apply H. omega. apply IHn. intros. apply H. omega.
Qed.

Remark getN_setN_outside:
  forall vl q c n p,
  p + Z_of_nat n <= q \/ q + Z_of_nat (length vl) <= p ->
  getN n p (setN vl q c) = getN n p c.
Proof.
  intros. apply getN_exten. intros. apply setN_outside. omega. 
Qed.

Lemma store_noread_undef:
  forall m ch b ofs (VA: valid_access m ch b ofs Writable) v,
       forall b' ofs', 
       perm m b' ofs' Readable \/ 
        update b (setN (encode_val ch v) ofs (mem_contents m b)) (mem_contents m) b' ofs' = Undef.
Proof.
  intros.
  destruct VA as [? _].
  unfold update.
  destruct (zeq b' b).
  subst b'.
  assert (ofs <= ofs' < ofs + size_chunk ch \/ (ofs' < ofs \/ ofs' >= ofs + size_chunk ch)) by omega.
  destruct H0.
  exploit (H ofs'); auto; intro.
  eauto with mem.
  rewrite setN_outside.
  destruct (noread_undef m b ofs'); auto.
  rewrite encode_val_length. rewrite <- size_chunk_conv; auto.
  destruct (noread_undef m b' ofs'); auto.
Qed.

(** [store chunk m b ofs v] perform a write in memory state [m].
  Value [v] is stored at address [b] and offset [ofs].
  Return the updated memory store, or [None] if the accessed bytes
  are not writable. *)

Definition store (chunk: memory_chunk) (m: mem) (b: block) (ofs: Z) (v: val): option mem :=
 match valid_access_dec m chunk b ofs Writable with
 | left VA => Some (mkmem (update b 
                                  (setN (encode_val chunk v) ofs (m.(mem_contents) b))
                                  m.(mem_contents))
                    m.(mem_access)
                    m.(bounds)
                    m.(nextblock)
                    m.(nextblock_pos)
                    m.(nextblock_noaccess)
                    m.(bounds_noaccess)
                    (store_noread_undef m chunk b ofs VA v))
 | right _ => None
 end.

(** [storev chunk m addr v] is similar, but the address and offset are given
  as a single value [addr], which must be a pointer value. *)

Definition storev (chunk: memory_chunk) (m: mem) (addr v: val) : option mem :=
  match addr with
  | Vptr b ofs => store chunk m b (Int.signed ofs) v
  | _ => None
  end.

(** [drop_perm m b lo hi p] sets the permissions of the byte range
    [(b, lo) ... (b, hi - 1)] to [p].  These bytes must have permissions
    at least [p] in the initial memory state [m].
    Returns updated memory state, or [None] if insufficient permissions. *)

Program Definition drop_perm (m: mem) (b: block) (lo hi: Z) (p: permission): option mem :=
  if range_perm_dec m b lo hi p then
    Some (mkmem (update b 
                        (fun ofs => if zle lo ofs && zlt ofs hi && negb (perm_order_dec p Readable)
                                    then Undef else m.(mem_contents) b ofs)
                        m.(mem_contents))
                (update b
                        (fun ofs => if zle lo ofs && zlt ofs hi then Some p else m.(mem_access) b ofs)
                        m.(mem_access))
                m.(bounds) m.(nextblock) _ _ _ _)
  else None.
Next Obligation.
  destruct m; auto.
Qed.
Next Obligation.
  destruct m; auto.
Qed.
Next Obligation.
  unfold update. destruct (zeq b0 b). subst b0.
  destruct (zle lo ofs). destruct (zlt ofs hi).
  exploit range_perm_in_bounds; eauto. omega. intros. omegaContradiction. 
  simpl. eapply bounds_noaccess; eauto. 
  simpl. eapply bounds_noaccess; eauto.
  eapply bounds_noaccess; eauto. 
Qed.
Next Obligation.
  unfold update. destruct (zeq b0 b). subst b0. 
  destruct (zle lo ofs && zlt ofs hi). 
  destruct (perm_order_dec p Readable); simpl; auto.
  eapply noread_undef; eauto.
  eapply noread_undef; eauto.
Qed.

(** * Properties of the memory operations *)

(** Properties of the empty store. *)

Theorem nextblock_empty: nextblock empty = 1.
Proof. reflexivity. Qed.

Theorem perm_empty: forall b ofs p, ~perm empty b ofs p.
Proof. 
  intros. unfold perm, empty; simpl. congruence.
Qed.

Theorem valid_access_empty: forall chunk b ofs p, ~valid_access empty chunk b ofs p.
Proof.
  intros. red; intros. elim (perm_empty b ofs p). apply H. 
  generalize (size_chunk_pos chunk); omega.
Qed.

(** ** Properties related to [load] *)

Theorem valid_access_load:
  forall m chunk b ofs,
  valid_access m chunk b ofs Readable ->
  exists v, load chunk m b ofs = Some v.
Proof.
  intros. econstructor. unfold load. rewrite pred_dec_true; eauto.  
Qed.

Theorem load_valid_access:
  forall m chunk b ofs v,
  load chunk m b ofs = Some v ->
  valid_access m chunk b ofs Readable.
Proof.
  intros until v. unfold load. 
  destruct (valid_access_dec m chunk b ofs Readable); intros.
  auto. 
  congruence.
Qed.

Lemma load_result:
  forall chunk m b ofs v,
  load chunk m b ofs = Some v ->
  v = decode_val chunk (getN (size_chunk_nat chunk) ofs (m.(mem_contents) b)).
Proof.
  intros until v. unfold load. 
  destruct (valid_access_dec m chunk b ofs Readable); intros.
  congruence.
  congruence.
Qed.

Hint Local Resolve load_valid_access valid_access_load: mem.

Theorem load_type:
  forall m chunk b ofs v,
  load chunk m b ofs = Some v ->
  Val.has_type v (type_of_chunk chunk).
Proof.
  intros. exploit load_result; eauto; intros. rewrite H0. 
  apply decode_val_type. 
Qed.

Theorem load_cast:
  forall m chunk b ofs v,
  load chunk m b ofs = Some v ->
  match chunk with
  | Mint8signed => v = Val.sign_ext 8 v
  | Mint8unsigned => v = Val.zero_ext 8 v
  | Mint16signed => v = Val.sign_ext 16 v
  | Mint16unsigned => v = Val.zero_ext 16 v
  | Mfloat32 => v = Val.singleoffloat v
  | _ => True
  end.
Proof.
  intros. exploit load_result; eauto.
  set (l := getN (size_chunk_nat chunk) ofs (mem_contents m b)).
  intros. subst v. apply decode_val_cast. 
Qed.

Theorem load_int8_signed_unsigned:
  forall m b ofs,
  load Mint8signed m b ofs = option_map (Val.sign_ext 8) (load Mint8unsigned m b ofs).
Proof.
  intros. unfold load.
  change (size_chunk_nat Mint8signed) with (size_chunk_nat Mint8unsigned).
  set (cl := getN (size_chunk_nat Mint8unsigned) ofs (mem_contents m b)).
  destruct (valid_access_dec m Mint8signed b ofs Readable).
  rewrite pred_dec_true; auto. unfold decode_val. 
  destruct (proj_bytes cl); auto. rewrite decode_int8_signed_unsigned. auto.
  rewrite pred_dec_false; auto.
Qed.

Theorem load_int16_signed_unsigned:
  forall m b ofs,
  load Mint16signed m b ofs = option_map (Val.sign_ext 16) (load Mint16unsigned m b ofs).
Proof.
  intros. unfold load.
  change (size_chunk_nat Mint16signed) with (size_chunk_nat Mint16unsigned).
  set (cl := getN (size_chunk_nat Mint16unsigned) ofs (mem_contents m b)).
  destruct (valid_access_dec m Mint16signed b ofs Readable).
  rewrite pred_dec_true; auto. unfold decode_val. 
  destruct (proj_bytes cl); auto. rewrite decode_int16_signed_unsigned. auto.
  rewrite pred_dec_false; auto.
Qed.

Theorem loadbytes_load:
  forall chunk m b ofs bytes,
  loadbytes m b ofs (size_chunk chunk) = Some bytes ->
  (align_chunk chunk | ofs) ->
  load chunk m b ofs = Some(decode_val chunk bytes).
Proof.
  unfold loadbytes, load; intros. 
  destruct (range_perm_dec m b ofs (ofs + size_chunk chunk) Readable);
  try congruence.
  inv H. rewrite pred_dec_true. auto. 
  split; auto.
Qed.

Theorem load_loadbytes:
  forall chunk m b ofs v,
  load chunk m b ofs = Some v ->
  exists bytes, loadbytes m b ofs (size_chunk chunk) = Some bytes
             /\ v = decode_val chunk bytes.
Proof.
  intros. exploit load_valid_access; eauto. intros [A B].
  exploit load_result; eauto. intros. 
  exists (getN (size_chunk_nat chunk) ofs (mem_contents m b)); split.
  unfold loadbytes. rewrite pred_dec_true; auto. 
  auto.
Qed.

Lemma getN_length:
  forall c n p, length (getN n p c) = n.
Proof.
  induction n; simpl; intros. auto. decEq; auto.
Qed.

Theorem loadbytes_length:
  forall m b ofs n bytes,
  loadbytes m b ofs n = Some bytes ->
  length bytes = nat_of_Z n.
Proof.
  unfold loadbytes; intros.
  destruct (range_perm_dec m b ofs (ofs + n) Readable); try congruence.
  inv H. apply getN_length.
Qed.

Lemma getN_concat:
  forall c n1 n2 p,
  getN (n1 + n2)%nat p c = getN n1 p c ++ getN n2 (p + Z_of_nat n1) c.
Proof.
  induction n1; intros.
  simpl. decEq. omega.
  rewrite inj_S. simpl. decEq.
  replace (p + Zsucc (Z_of_nat n1)) with ((p + 1) + Z_of_nat n1) by omega.
  auto. 
Qed.

Theorem loadbytes_concat:
  forall m b ofs n1 n2 bytes1 bytes2,
  loadbytes m b ofs n1 = Some bytes1 ->
  loadbytes m b (ofs + n1) n2 = Some bytes2 ->
  n1 >= 0 -> n2 >= 0 ->
  loadbytes m b ofs (n1 + n2) = Some(bytes1 ++ bytes2).
Proof.
  unfold loadbytes; intros.
  destruct (range_perm_dec m b ofs (ofs + n1) Readable); try congruence.
  destruct (range_perm_dec m b (ofs + n1) (ofs + n1 + n2) Readable); try congruence.
  rewrite pred_dec_true. rewrite nat_of_Z_plus; auto.
  rewrite getN_concat. rewrite nat_of_Z_eq; auto.
  congruence.
  red; intros. 
  assert (ofs0 < ofs + n1 \/ ofs0 >= ofs + n1) by omega.
  destruct H4. apply r; omega. apply r0; omega.
Qed.

Theorem loadbytes_split:
  forall m b ofs n1 n2 bytes,
  loadbytes m b ofs (n1 + n2) = Some bytes ->
  n1 >= 0 -> n2 >= 0 ->
  exists bytes1, exists bytes2,
     loadbytes m b ofs n1 = Some bytes1 
  /\ loadbytes m b (ofs + n1) n2 = Some bytes2
  /\ bytes = bytes1 ++ bytes2.
Proof.
  unfold loadbytes; intros. 
  destruct (range_perm_dec m b ofs (ofs + (n1 + n2)) Readable);
  try congruence.
  rewrite nat_of_Z_plus in H; auto. rewrite getN_concat in H.
  rewrite nat_of_Z_eq in H; auto. 
  repeat rewrite pred_dec_true.
  econstructor; econstructor.
  split. reflexivity. split. reflexivity. congruence.
  red; intros; apply r; omega.
  red; intros; apply r; omega.
Qed.

Theorem load_rep:
 forall ch m1 m2 b ofs v1 v2, 
  (forall z, 0 <= z < size_chunk ch -> mem_contents m1 b (ofs+z) = mem_contents m2 b (ofs+z)) ->
  load ch m1 b ofs = Some v1 ->
  load ch m2 b ofs = Some v2 ->
  v1 = v2.
Proof.
intros.
apply load_result in H0.
apply load_result in H1.
subst.
f_equal.
rewrite size_chunk_conv in H.
remember (size_chunk_nat ch) as n; clear Heqn.
revert ofs H; induction n; intros; simpl; auto.
f_equal.
rewrite inj_S in H.
replace ofs with (ofs+0) by omega.
apply H; omega.
apply IHn.
intros.
rewrite <- Zplus_assoc.
apply H.
rewrite inj_S. omega.
Qed.

(** ** Properties related to [store] *)

Theorem valid_access_store:
  forall m1 chunk b ofs v,
  valid_access m1 chunk b ofs Writable ->
  { m2: mem | store chunk m1 b ofs v = Some m2 }.
Proof.
  intros.
  unfold store. 
  destruct (valid_access_dec m1 chunk b ofs Writable).
  eauto.
  contradiction.
Qed.

Hint Local Resolve valid_access_store: mem.

Section STORE.
Variable chunk: memory_chunk.
Variable m1: mem.
Variable b: block.
Variable ofs: Z.
Variable v: val.
Variable m2: mem.
Hypothesis STORE: store chunk m1 b ofs v = Some m2.
(*
Lemma store_result:
  m2 = unchecked_store chunk m1 b ofs v.
Proof.
  unfold store in STORE.
  destruct (valid_access_dec m1 chunk b ofs Writable).
  congruence. 
  congruence.
Qed.
*)

Lemma store_access: mem_access m2 = mem_access m1.
Proof.
  unfold store in STORE. destruct ( valid_access_dec m1 chunk b ofs Writable); inv STORE.
  auto.
Qed.

Lemma store_mem_contents: mem_contents m2 = 
                                       update b (setN (encode_val chunk v) ofs (m1.(mem_contents) b)) m1.(mem_contents).
Proof.
  unfold store in STORE. destruct ( valid_access_dec m1 chunk b ofs Writable); inv STORE.
  auto.
Qed.

Theorem perm_store_1:
  forall b' ofs' p, perm m1 b' ofs' p -> perm m2 b' ofs' p.
Proof.
  intros. 
 unfold perm in *. rewrite store_access; auto.
Qed.

Theorem perm_store_2:
  forall b' ofs' p, perm m2 b' ofs' p -> perm m1 b' ofs' p.
Proof.
  intros. unfold perm in *.  rewrite store_access in H; auto.
Qed.

Hint Local Resolve perm_store_1 perm_store_2: mem.

Theorem nextblock_store:
  nextblock m2 = nextblock m1.
Proof.
  intros.
  unfold store in STORE. destruct ( valid_access_dec m1 chunk b ofs Writable); inv STORE.
  auto.
Qed.

Theorem store_valid_block_1:
  forall b', valid_block m1 b' -> valid_block m2 b'.
Proof.
  unfold valid_block; intros. rewrite nextblock_store; auto.
Qed.

Theorem store_valid_block_2:
  forall b', valid_block m2 b' -> valid_block m1 b'.
Proof.
  unfold valid_block; intros. rewrite nextblock_store in H; auto.
Qed.

Hint Local Resolve store_valid_block_1 store_valid_block_2: mem.

Theorem store_valid_access_1:
  forall chunk' b' ofs' p,
  valid_access m1 chunk' b' ofs' p -> valid_access m2 chunk' b' ofs' p.
Proof.
  intros. inv H. constructor; try red; auto with mem.
Qed.

Theorem store_valid_access_2:
  forall chunk' b' ofs' p,
  valid_access m2 chunk' b' ofs' p -> valid_access m1 chunk' b' ofs' p.
Proof.
  intros. inv H. constructor; try red; auto with mem.
Qed.

Theorem store_valid_access_3:
  valid_access m1 chunk b ofs Writable.
Proof.
  unfold store in STORE. destruct (valid_access_dec m1 chunk b ofs Writable).
  auto. 
  congruence.
Qed.

Hint Local Resolve store_valid_access_1 store_valid_access_2
             store_valid_access_3: mem.

Theorem bounds_store:
  forall b', bounds m2 b' = bounds m1 b'.
Proof.
  intros.
  unfold store in STORE.
  destruct ( valid_access_dec m1 chunk b ofs Writable); inv STORE. simpl. auto.
Qed.

Theorem load_store_similar:
  forall chunk',
  size_chunk chunk' = size_chunk chunk ->
  exists v', load chunk' m2 b ofs = Some v' /\ decode_encode_val v chunk chunk' v'.
Proof.
  intros.
  exploit (valid_access_load m2 chunk').
    eapply valid_access_compat. symmetry; eauto. eauto with mem. 
  intros [v' LOAD].
  exists v'; split; auto.
  exploit load_result; eauto. intros B. 
  rewrite B. rewrite store_mem_contents; simpl. 
  rewrite update_s.
  replace (size_chunk_nat chunk') with (length (encode_val chunk v)).
  rewrite getN_setN_same. apply decode_encode_val_general. 
  rewrite encode_val_length. repeat rewrite size_chunk_conv in H. 
  apply inj_eq_rev; auto.
Qed.

Theorem load_store_same:
  Val.has_type v (type_of_chunk chunk) ->
  load chunk m2 b ofs = Some (Val.load_result chunk v).
Proof.
  intros.
  destruct (load_store_similar chunk) as [v' [A B]]. auto.
  rewrite A. decEq. eapply decode_encode_val_similar; eauto. 
Qed.

Theorem load_store_other:
  forall chunk' b' ofs',
  b' <> b
  \/ ofs' + size_chunk chunk' <= ofs
  \/ ofs + size_chunk chunk <= ofs' ->
  load chunk' m2 b' ofs' = load chunk' m1 b' ofs'.
Proof.
  intros. unfold load. 
  destruct (valid_access_dec m1 chunk' b' ofs' Readable).
  rewrite pred_dec_true. 
  decEq. decEq. rewrite store_mem_contents; simpl.
  unfold update. destruct (zeq b' b). subst b'.
  apply getN_setN_outside. rewrite encode_val_length. repeat rewrite <- size_chunk_conv.
  intuition.
  auto.
  eauto with mem.
  rewrite pred_dec_false. auto.
  eauto with mem. 
Qed.

Theorem loadbytes_store_same:
  loadbytes m2 b ofs (size_chunk chunk) = Some(encode_val chunk v).
Proof.
  intros.
  assert (valid_access m2 chunk b ofs Readable) by eauto with mem.
  unfold loadbytes. rewrite pred_dec_true. rewrite store_mem_contents; simpl. 
  rewrite update_s. 
  replace (nat_of_Z (size_chunk chunk))
     with (length (encode_val chunk v)).
  rewrite getN_setN_same. auto.
  rewrite encode_val_length. auto.
  apply H. 
Qed.

Theorem loadbytes_store_other:
  forall b' ofs' n,
  b' <> b
  \/ n <= 0
  \/ ofs' + n <= ofs
  \/ ofs + size_chunk chunk <= ofs' ->
  loadbytes m2 b' ofs' n = loadbytes m1 b' ofs' n.
Proof.
  intros. unfold loadbytes. 
  destruct (range_perm_dec m1 b' ofs' (ofs' + n) Readable).
  rewrite pred_dec_true. 
  decEq. rewrite store_mem_contents; simpl.
  unfold update. destruct (zeq b' b). subst b'.
  destruct H. congruence.
  destruct (zle n 0). 
  rewrite (nat_of_Z_neg _ z). auto.
  destruct H. omegaContradiction.
  apply getN_setN_outside. rewrite encode_val_length. rewrite <- size_chunk_conv.
  rewrite nat_of_Z_eq. auto. omega. 
  auto.
  red; intros. eauto with mem.
  rewrite pred_dec_false. auto.
  red; intro; elim n0; red; intros; eauto with mem.
Qed.

Lemma setN_property:
  forall (P: memval -> Prop) vl p q c,
  (forall v, In v vl -> P v) ->
  p <= q < p + Z_of_nat (length vl) ->
  P(setN vl p c q).
Proof.
  induction vl; intros.
  simpl in H0. omegaContradiction.
  simpl length in H0. rewrite inj_S in H0. simpl. 
  destruct (zeq p q). subst q. rewrite setN_outside. rewrite update_s. 
  auto with coqlib. omega.
  apply IHvl. auto with coqlib. omega.
Qed.

Lemma getN_in:
  forall c q n p,
  p <= q < p + Z_of_nat n ->
  In (c q) (getN n p c).
Proof.
  induction n; intros.
  simpl in H; omegaContradiction.
  rewrite inj_S in H. simpl. destruct (zeq p q).
  subst q. auto.
  right. apply IHn. omega. 
Qed.

Theorem load_pointer_store:
  forall chunk' b' ofs' v_b v_o,
  load chunk' m2 b' ofs' = Some(Vptr v_b v_o) ->
  (chunk = Mint32 /\ v = Vptr v_b v_o /\ chunk' = Mint32 /\ b' = b /\ ofs' = ofs)
  \/ (b' <> b \/ ofs' + size_chunk chunk' <= ofs \/ ofs + size_chunk chunk <= ofs').
Proof.
  intros. exploit load_result; eauto. rewrite store_mem_contents; simpl. 
  unfold update. destruct (zeq b' b); auto. subst b'. intro DEC.
  destruct (zle (ofs' + size_chunk chunk') ofs); auto.
  destruct (zle (ofs + size_chunk chunk) ofs'); auto.
  destruct (size_chunk_nat_pos chunk) as [sz SZ].
  destruct (size_chunk_nat_pos chunk') as [sz' SZ'].
  exploit decode_pointer_shape; eauto. intros [CHUNK' PSHAPE]. clear CHUNK'.
  generalize (encode_val_shape chunk v). intro VSHAPE.  
  set (c := mem_contents m1 b) in *.
  set (c' := setN (encode_val chunk v) ofs c) in *.
  destruct (zeq ofs ofs').

(* 1.  ofs = ofs':  must be same chunks and same value *)
  subst ofs'. inv VSHAPE. 
  exploit decode_val_pointer_inv; eauto. intros [A B].
  subst chunk'. simpl in B. inv B.
  generalize H4. unfold c'. rewrite <- H0. simpl. 
  rewrite setN_outside; try omega. rewrite update_s. intros.
  exploit (encode_val_pointer_inv chunk v v_b v_o). 
  rewrite <- H0. subst mv1. eauto. intros [C [D E]].
  left; auto.

  destruct (zlt ofs ofs').

(* 2. ofs < ofs':

      ofs   ofs'   ofs+|chunk|
       [-------------------]       write
            [-------------------]  read

   The byte at ofs' satisfies memval_valid_cont (consequence of write).
   For the read to return a pointer, it must satisfy ~memval_valid_cont. 
*)
  elimtype False.
  assert (~memval_valid_cont (c' ofs')).
    rewrite SZ' in PSHAPE. simpl in PSHAPE. inv PSHAPE. auto.
  assert (memval_valid_cont (c' ofs')).
    inv VSHAPE. unfold c'. rewrite <- H1. simpl. 
    apply setN_property. auto.
    assert (length mvl = sz). 
      generalize (encode_val_length chunk v). rewrite <- H1. rewrite SZ. 
      simpl; congruence.
    rewrite H4. rewrite size_chunk_conv in z0. omega. 
  contradiction.

(* 3. ofs > ofs':

      ofs'   ofs   ofs'+|chunk'|
              [-------------------]  write
        [----------------]           read

   The byte at ofs satisfies memval_valid_first (consequence of write).
   For the read to return a pointer, it must satisfy ~memval_valid_first.
*)
  elimtype False.
  assert (memval_valid_first (c' ofs)).
    inv VSHAPE. unfold c'. rewrite <- H0. simpl. 
    rewrite setN_outside. rewrite update_s. auto. omega.
  assert (~memval_valid_first (c' ofs)).
    rewrite SZ' in PSHAPE. simpl in PSHAPE. inv PSHAPE. 
    apply H4. apply getN_in. rewrite size_chunk_conv in z. 
    rewrite SZ' in z. rewrite inj_S in z. omega. 
  contradiction.
Qed.

End STORE.

Hint Local Resolve perm_store_1 perm_store_2: mem.
Hint Local Resolve store_valid_block_1 store_valid_block_2: mem.
Hint Local Resolve store_valid_access_1 store_valid_access_2
             store_valid_access_3: mem.

Theorem load_store_pointer_overlap:
  forall chunk m1 b ofs v_b v_o m2 chunk' ofs' v,
  store chunk m1 b ofs (Vptr v_b v_o) = Some m2 ->
  load chunk' m2 b ofs' = Some v ->
  ofs' <> ofs ->
  ofs' + size_chunk chunk' > ofs ->
  ofs + size_chunk chunk > ofs' ->
  v = Vundef.
Proof.
  intros.
  exploit store_mem_contents; eauto. intro ST.
  exploit load_result; eauto. intro LD.
  rewrite LD; clear LD.
Opaque encode_val.
  rewrite ST; simpl.
  rewrite update_s.
  set (c := mem_contents m1 b).
  set (c' := setN (encode_val chunk (Vptr v_b v_o)) ofs c).
  destruct (decode_val_shape chunk' (getN (size_chunk_nat chunk') ofs' c'))
  as [OK | VSHAPE].
  apply getN_length. 
  exact OK.
  elimtype False.
  destruct (size_chunk_nat_pos chunk) as [sz SZ]. 
  destruct (size_chunk_nat_pos chunk') as [sz' SZ']. 
  assert (ENC: encode_val chunk (Vptr v_b v_o) = list_repeat (size_chunk_nat chunk) Undef
               \/ pointer_encoding_shape (encode_val chunk (Vptr v_b v_o))).
  destruct chunk; try (left; reflexivity). 
  right. apply encode_pointer_shape. 
  assert (GET: getN (size_chunk_nat chunk) ofs c' = encode_val chunk (Vptr v_b v_o)).
  unfold c'. rewrite <- (encode_val_length chunk (Vptr v_b v_o)). 
  apply getN_setN_same.
  destruct (zlt ofs ofs').

(* ofs < ofs':

      ofs   ofs'   ofs+|chunk|
       [-------------------]       write
            [-------------------]  read

   The byte at ofs' is Undef or not memval_valid_first (because write of pointer).
   The byte at ofs' must be memval_valid_first and not Undef (otherwise load returns Vundef).
*)
  assert (memval_valid_first (c' ofs') /\ c' ofs' <> Undef).
    rewrite SZ' in VSHAPE. simpl in VSHAPE. inv VSHAPE. auto.
  assert (~memval_valid_first (c' ofs') \/ c' ofs' = Undef).
    unfold c'. destruct ENC.
    right. apply setN_property. rewrite H5. intros. eapply in_list_repeat; eauto.
    rewrite encode_val_length. rewrite <- size_chunk_conv. omega.
    left. revert H5. rewrite <- GET. rewrite SZ. simpl. intros. inv H5.
    apply setN_property. apply H9. rewrite getN_length.
    rewrite size_chunk_conv in H3. rewrite SZ in H3. rewrite inj_S in H3. omega. 
  intuition. 

(* ofs > ofs':

      ofs'   ofs   ofs'+|chunk'|
              [-------------------]  write
        [----------------]           read

   The byte at ofs is Undef or not memval_valid_cont (because write of pointer).
   The byte at ofs must be memval_valid_cont and not Undef (otherwise load returns Vundef).
*)
  assert (memval_valid_cont (c' ofs) /\ c' ofs <> Undef).
    rewrite SZ' in VSHAPE. simpl in VSHAPE. inv VSHAPE. 
    apply H8. apply getN_in. rewrite size_chunk_conv in H2. 
    rewrite SZ' in H2. rewrite inj_S in H2. omega. 
  assert (~memval_valid_cont (c' ofs) \/ c' ofs = Undef).
    elim ENC. 
    rewrite <- GET. rewrite SZ. simpl. intros. right; congruence.
    rewrite <- GET. rewrite SZ. simpl. intros. inv H5. auto.
  intuition.
Qed.

Theorem load_store_pointer_mismatch:
  forall chunk m1 b ofs v_b v_o m2 chunk' v,
  store chunk m1 b ofs (Vptr v_b v_o) = Some m2 ->
  load chunk' m2 b ofs = Some v ->
  chunk <> Mint32 \/ chunk' <> Mint32 ->
  v = Vundef.
Proof.
  intros.
  exploit store_mem_contents; eauto. intro ST.
  exploit load_result; eauto. intro LD.
  rewrite LD; clear LD.
Opaque encode_val.
  rewrite ST; simpl.
  rewrite update_s.
  set (c1 := mem_contents m1 b).
  set (e := encode_val chunk (Vptr v_b v_o)).
  destruct (size_chunk_nat_pos chunk) as [sz SZ].
  destruct (size_chunk_nat_pos chunk') as [sz' SZ'].
  assert (match e with
          | Undef :: _ => True
          | Pointer _ _ _ :: _ => chunk = Mint32
          | _ => False
          end).
Transparent encode_val.
  unfold e, encode_val. rewrite SZ. destruct chunk; simpl; auto.
  destruct e as [ | e1 el]. contradiction.
  rewrite SZ'. simpl. rewrite setN_outside. rewrite update_s. 
  destruct e1; try contradiction. 
  destruct chunk'; auto. 
  destruct chunk'; auto. intuition.
  omega.
Qed.

Lemma store_similar_chunks:
  forall chunk1 chunk2 v1 v2 m b ofs,
  encode_val chunk1 v1 = encode_val chunk2 v2 ->
  store chunk1 m b ofs v1 = store chunk2 m b ofs v2.
Proof.
  intros. unfold store. 
  assert (size_chunk chunk1 = size_chunk chunk2).
    repeat rewrite size_chunk_conv.
    rewrite <- (encode_val_length chunk1 v1).
    rewrite <- (encode_val_length chunk2 v2).
    congruence.
  unfold store.
  destruct (valid_access_dec m chunk1 b ofs Writable);
  destruct (valid_access_dec m chunk2 b ofs Writable); auto.
  f_equal. apply mkmem_ext; auto. congruence.
  elimtype False.
  destruct chunk1; destruct chunk2;  inv H0; unfold valid_access, align_chunk in *; try contradiction.
  elimtype False.
  destruct chunk1; destruct chunk2;  inv H0; unfold valid_access, align_chunk in *; try contradiction.
Qed.


Theorem store_signed_unsigned_8:
  forall m b ofs v,
  store Mint8signed m b ofs v = store Mint8unsigned m b ofs v.
Proof. intros. apply store_similar_chunks. apply encode_val_int8_signed_unsigned. Qed.

Theorem store_signed_unsigned_16:
  forall m b ofs v,
  store Mint16signed m b ofs v = store Mint16unsigned m b ofs v.
Proof. intros. apply store_similar_chunks. apply encode_val_int16_signed_unsigned. Qed.

Theorem store_int8_zero_ext:
  forall m b ofs n,
  store Mint8unsigned m b ofs (Vint (Int.zero_ext 8 n)) =
  store Mint8unsigned m b ofs (Vint n).
Proof. intros. apply store_similar_chunks. apply encode_val_int8_zero_ext. Qed.

Theorem store_int8_sign_ext:
  forall m b ofs n,
  store Mint8signed m b ofs (Vint (Int.sign_ext 8 n)) =
  store Mint8signed m b ofs (Vint n).
Proof. intros. apply store_similar_chunks. apply encode_val_int8_sign_ext. Qed.

Theorem store_int16_zero_ext:
  forall m b ofs n,
  store Mint16unsigned m b ofs (Vint (Int.zero_ext 16 n)) =
  store Mint16unsigned m b ofs (Vint n).
Proof. intros. apply store_similar_chunks. apply encode_val_int16_zero_ext. Qed.

Theorem store_int16_sign_ext:
  forall m b ofs n,
  store Mint16signed m b ofs (Vint (Int.sign_ext 16 n)) =
  store Mint16signed m b ofs (Vint n).
Proof. intros. apply store_similar_chunks. apply encode_val_int16_sign_ext. Qed.

Theorem store_float32_truncate:
  forall m b ofs n,
  store Mfloat32 m b ofs (Vfloat (Float.singleoffloat n)) =
  store Mfloat32 m b ofs (Vfloat n).
Proof. intros. apply store_similar_chunks. simpl. decEq. apply encode_float32_cast. Qed.

(** ** Properties related to [alloc]. *)

Section ALLOC.

Variable m1: mem.
Variables lo hi: Z.
Variable m2: mem.
Variable b: block.
Hypothesis ALLOC: alloc m1 lo hi = (m2, b).

Theorem nextblock_alloc:
  nextblock m2 = Zsucc (nextblock m1).
Proof.
  injection ALLOC; intros. rewrite <- H0; auto.
Qed.

Theorem alloc_result:
  b = nextblock m1.
Proof.
  injection ALLOC; auto.
Qed.

Theorem valid_block_alloc:
  forall b', valid_block m1 b' -> valid_block m2 b'.
Proof.
  unfold valid_block; intros. rewrite nextblock_alloc. omega.
Qed.

Theorem fresh_block_alloc:
  ~(valid_block m1 b).
Proof.
  unfold valid_block. rewrite alloc_result. omega.
Qed.

Theorem valid_new_block:
  valid_block m2 b.
Proof.
  unfold valid_block. rewrite alloc_result. rewrite nextblock_alloc. omega.
Qed.

Hint Local Resolve valid_block_alloc fresh_block_alloc valid_new_block: mem.

Theorem valid_block_alloc_inv:
  forall b', valid_block m2 b' -> b' = b \/ valid_block m1 b'.
Proof.
  unfold valid_block; intros. 
  rewrite nextblock_alloc in H. rewrite alloc_result. 
  unfold block; omega.
Qed.

Theorem perm_alloc_1:
  forall b' ofs p, perm m1 b' ofs p -> perm m2 b' ofs p.
Proof.
  unfold perm; intros. injection ALLOC; intros. rewrite <- H1; simpl.
  subst b. unfold update. destruct (zeq b' (nextblock m1)); auto.
  elimtype False.
  destruct (nextblock_noaccess m1 b').
  omega.
  rewrite bounds_noaccess in H. contradiction. rewrite H0.  simpl; omega.
Qed.

Theorem perm_alloc_2:
  forall ofs, lo <= ofs < hi -> perm m2 b ofs Freeable.
Proof.
  unfold perm; intros. injection ALLOC; intros. rewrite <- H1; simpl.
  subst b. rewrite update_s. unfold proj_sumbool. rewrite zle_true.
  rewrite zlt_true. simpl. auto with mem. omega. omega.
Qed.

Theorem perm_alloc_3:
  forall ofs p, ofs < lo \/ hi <= ofs -> ~perm m2 b ofs p.
Proof.
  unfold perm; intros. injection ALLOC; intros. rewrite <- H1; simpl.
  subst b. rewrite update_s. unfold proj_sumbool.
  destruct H. rewrite zle_false. simpl. congruence. omega.
  rewrite zlt_false. rewrite andb_false_r.
  intro; contradiction.
  omega.
Qed.

Hint Local Resolve perm_alloc_1 perm_alloc_2 perm_alloc_3: mem.

Theorem perm_alloc_inv:
  forall b' ofs p, 
  perm m2 b' ofs p ->
  if zeq b' b then lo <= ofs < hi else perm m1 b' ofs p.
Proof.
  intros until p; unfold perm. inv ALLOC. simpl. 
  unfold update. destruct (zeq b' (nextblock m1)); intros.
  destruct (zle lo ofs); try contradiction. destruct (zlt ofs hi); try contradiction.
  split; auto. 
  auto.
Qed.

Theorem valid_access_alloc_other:
  forall chunk b' ofs p,
  valid_access m1 chunk b' ofs p ->
  valid_access m2 chunk b' ofs p.
Proof.
  intros. inv H. constructor; auto with mem.
  red; auto with mem.
Qed.

Theorem valid_access_alloc_same:
  forall chunk ofs,
  lo <= ofs -> ofs + size_chunk chunk <= hi -> (align_chunk chunk | ofs) ->
  valid_access m2 chunk b ofs Freeable.
Proof.
  intros. constructor; auto with mem.
  red; intros. apply perm_alloc_2. omega. 
Qed.

Hint Local Resolve valid_access_alloc_other valid_access_alloc_same: mem.

Theorem valid_access_alloc_inv:
  forall chunk b' ofs p,
  valid_access m2 chunk b' ofs p ->
  if eq_block b' b
  then lo <= ofs /\ ofs + size_chunk chunk <= hi /\ (align_chunk chunk | ofs)
  else valid_access m1 chunk b' ofs p.
Proof.
  intros. inv H.
  generalize (size_chunk_pos chunk); intro.
  unfold eq_block. destruct (zeq b' b). subst b'.
  assert (perm m2 b ofs p). apply H0. omega. 
  assert (perm m2 b (ofs + size_chunk chunk - 1) p). apply H0. omega. 
  exploit perm_alloc_inv. eexact H2. rewrite zeq_true. intro.
  exploit perm_alloc_inv. eexact H3. rewrite zeq_true. intro. 
  intuition omega. 
  split; auto. red; intros. 
  exploit perm_alloc_inv. apply H0. eauto. rewrite zeq_false; auto. 
Qed.

Theorem bounds_alloc:
  forall b', bounds m2 b' = if eq_block b' b then (lo, hi) else bounds m1 b'.
Proof.
  injection ALLOC; intros. rewrite <- H; rewrite <- H0; simpl. 
  unfold update. auto. 
Qed.

Theorem bounds_alloc_same:
  bounds m2 b = (lo, hi).
Proof.
  rewrite bounds_alloc. apply dec_eq_true. 
Qed. 

Theorem bounds_alloc_other:
  forall b', b' <> b -> bounds m2 b' = bounds m1 b'.
Proof.
  intros. rewrite bounds_alloc. apply dec_eq_false. auto.
Qed.

Theorem load_alloc_unchanged:
  forall chunk b' ofs,
  valid_block m1 b' ->
  load chunk m2 b' ofs = load chunk m1 b' ofs.
Proof.
  intros. unfold load.
  destruct (valid_access_dec m2 chunk b' ofs Readable).
  exploit valid_access_alloc_inv; eauto. destruct (eq_block b' b); intros.
  subst b'. elimtype False. eauto with mem.
  rewrite pred_dec_true; auto.
  injection ALLOC; intros. rewrite <- H2; simpl.
  rewrite update_o. auto. rewrite H1. apply sym_not_equal; eauto with mem.
  rewrite pred_dec_false. auto.
  eauto with mem.
Qed.

Theorem load_alloc_other:
  forall chunk b' ofs v,
  load chunk m1 b' ofs = Some v ->
  load chunk m2 b' ofs = Some v.
Proof.
  intros. rewrite <- H. apply load_alloc_unchanged. eauto with mem.
Qed.

Theorem load_alloc_same:
  forall chunk ofs v,
  load chunk m2 b ofs = Some v ->
  v = Vundef.
Proof.
  intros. exploit load_result; eauto. intro. rewrite H0. 
  injection ALLOC; intros. rewrite <- H2; simpl. rewrite <- H1.
  rewrite update_s. destruct chunk; reflexivity. 
Qed.

Theorem load_alloc_same':
  forall chunk ofs,
  lo <= ofs -> ofs + size_chunk chunk <= hi -> (align_chunk chunk | ofs) ->
  load chunk m2 b ofs = Some Vundef.
Proof.
  intros. assert (exists v, load chunk m2 b ofs = Some v).
    apply valid_access_load. constructor; auto.
    red; intros. eapply perm_implies. apply perm_alloc_2. omega. auto with mem.
  destruct H2 as [v LOAD]. rewrite LOAD. decEq.
  eapply load_alloc_same; eauto.
Qed.

End ALLOC.

Hint Local Resolve valid_block_alloc fresh_block_alloc valid_new_block: mem.
Hint Local Resolve valid_access_alloc_other valid_access_alloc_same: mem.

(** ** Properties related to [free]. *)

Theorem range_perm_free:
  forall m1 b lo hi,
  range_perm m1 b lo hi Freeable ->
  { m2: mem | free m1 b lo hi = Some m2 }.
Proof.
  intros; unfold free. rewrite pred_dec_true; auto. econstructor; eauto.
Qed.

Section FREE.

Variable m1: mem.
Variable bf: block.
Variables lo hi: Z.
Variable m2: mem.
Hypothesis FREE: free m1 bf lo hi = Some m2.

Theorem free_range_perm:
  range_perm m1 bf lo hi Freeable.
Proof.
  unfold free in FREE. destruct (range_perm_dec m1 bf lo hi Freeable); auto.
  congruence.
Qed.

Lemma free_result:
  m2 = unchecked_free m1 bf lo hi.
Proof.
  unfold free in FREE. destruct (range_perm_dec m1 bf lo hi Freeable).
  congruence. congruence.
Qed.

Theorem nextblock_free:
  nextblock m2 = nextblock m1.
Proof.
  rewrite free_result; reflexivity.
Qed.

Theorem valid_block_free_1:
  forall b, valid_block m1 b -> valid_block m2 b.
Proof.
  intros. rewrite free_result. assumption.
Qed.

Theorem valid_block_free_2:
  forall b, valid_block m2 b -> valid_block m1 b.
Proof.
  intros. rewrite free_result in H. assumption.
Qed.

Hint Local Resolve valid_block_free_1 valid_block_free_2: mem.

Theorem perm_free_1:
  forall b ofs p,
  b <> bf \/ ofs < lo \/ hi <= ofs ->
  perm m1 b ofs p ->
  perm m2 b ofs p.
Proof.
  intros. rewrite free_result. unfold perm, unchecked_free; simpl.
  unfold update. destruct (zeq b bf). subst b.
  destruct (zle lo ofs); simpl. 
  destruct (zlt ofs hi); simpl.
  elimtype False; intuition.
  auto. auto.
  auto.
Qed.

Theorem perm_free_2:
  forall ofs p, lo <= ofs < hi -> ~ perm m2 bf ofs p.
Proof.
  intros. rewrite free_result. unfold perm, unchecked_free; simpl.
  rewrite update_s. unfold proj_sumbool. rewrite zle_true. rewrite zlt_true. 
  simpl. congruence. omega. omega.
Qed.

Theorem perm_free_3:
  forall b ofs p,
  perm m2 b ofs p -> perm m1 b ofs p.
Proof.
  intros until p. rewrite free_result. unfold perm, unchecked_free; simpl.
  unfold update. destruct (zeq b bf). subst b. 
  destruct (zle lo ofs); simpl. 
  destruct (zlt ofs hi); simpl. intro; contradiction.
  congruence. auto. auto.
Qed.

Theorem valid_access_free_1:
  forall chunk b ofs p,
  valid_access m1 chunk b ofs p -> 
  b <> bf \/ lo >= hi \/ ofs + size_chunk chunk <= lo \/ hi <= ofs ->
  valid_access m2 chunk b ofs p.
Proof.
  intros. inv H. constructor; auto with mem.
  red; intros. eapply perm_free_1; eauto.
  destruct (zlt lo hi). intuition. right. omega. 
Qed.

Theorem valid_access_free_2:
  forall chunk ofs p,
  lo < hi -> ofs + size_chunk chunk > lo -> ofs < hi ->
  ~(valid_access m2 chunk bf ofs p).
Proof.
  intros; red; intros. inv H2. 
  generalize (size_chunk_pos chunk); intros.
  destruct (zlt ofs lo).
  elim (perm_free_2 lo p).
  omega. apply H3. omega. 
  elim (perm_free_2 ofs p).
  omega. apply H3. omega. 
Qed.

Theorem valid_access_free_inv_1:
  forall chunk b ofs p,
  valid_access m2 chunk b ofs p ->
  valid_access m1 chunk b ofs p.
Proof.
  intros. destruct H. split; auto. 
  red; intros. generalize (H ofs0 H1). 
  rewrite free_result. unfold perm, unchecked_free; simpl. 
  unfold update. destruct (zeq b bf). subst b. 
  destruct (zle lo ofs0); simpl.
  destruct (zlt ofs0 hi); simpl. 
  intro; contradiction. congruence. auto. auto.
Qed.

Theorem valid_access_free_inv_2:
  forall chunk ofs p,
  valid_access m2 chunk bf ofs p ->
  lo >= hi \/ ofs + size_chunk chunk <= lo \/ hi <= ofs.
Proof.
  intros.
  destruct (zlt lo hi); auto. 
  destruct (zle (ofs + size_chunk chunk) lo); auto.
  destruct (zle hi ofs); auto.
  elim (valid_access_free_2 chunk ofs p); auto. omega.
Qed.

Theorem bounds_free:
  forall b, bounds m2 b = bounds m1 b.
Proof.
  intros. rewrite free_result; simpl. auto.
Qed.

Theorem load_free:
  forall chunk b ofs,
  b <> bf \/ lo >= hi \/ ofs + size_chunk chunk <= lo \/ hi <= ofs ->
  load chunk m2 b ofs = load chunk m1 b ofs.
Proof.
  intros. unfold load.
  destruct (valid_access_dec m2 chunk b ofs Readable).
  rewrite pred_dec_true. 
  rewrite free_result; auto.
  simpl. f_equal. f_equal.
  unfold clearN.
  rewrite size_chunk_conv in H.
  remember (size_chunk_nat chunk) as n; clear Heqn.
  clear v FREE.
  revert lo hi ofs H; induction n; intros; simpl; auto.
  f_equal.
  destruct (zeq b bf); auto. subst bf.
  destruct (zle lo ofs); auto. destruct (zlt ofs hi); auto.
  elimtype False.
  destruct H as [? | [? | [? | ?]]]; try omega.
  contradict H; auto.
  rewrite inj_S in H; omega.
  apply IHn.
  rewrite inj_S in H.
  destruct H as [? | [? | [? | ?]]]; auto.
  unfold block in *; omega.
  unfold block in *; omega.

  apply valid_access_free_inv_1; auto. 
  rewrite pred_dec_false; auto.
  red; intro; elim n. eapply valid_access_free_1; eauto. 
Qed.

End FREE.

Hint Local Resolve valid_block_free_1 valid_block_free_2
             perm_free_1 perm_free_2 perm_free_3 
             valid_access_free_1 valid_access_free_inv_1: mem.

(** ** Properties related to [drop_perm] *)

Theorem range_perm_drop_1:
  forall m b lo hi p m', drop_perm m b lo hi p = Some m' -> range_perm m b lo hi p.
Proof.
  unfold drop_perm; intros. 
  destruct (range_perm_dec m b lo hi p). auto. discriminate.
Qed.

Theorem range_perm_drop_2:
  forall m b lo hi p,
  range_perm m b lo hi p -> {m' | drop_perm m b lo hi p = Some m' }.
Proof.
  unfold drop_perm; intros. 
  destruct (range_perm_dec m b lo hi p). econstructor. eauto. contradiction.
Qed.

Section DROP.

Variable m: mem.
Variable b: block.
Variable lo hi: Z.
Variable p: permission.
Variable m': mem.
Hypothesis DROP: drop_perm m b lo hi p = Some m'.

Theorem nextblock_drop:
  nextblock m' = nextblock m.
Proof.
  unfold drop_perm in DROP. destruct (range_perm_dec m b lo hi p); inv DROP; auto.
Qed.

Theorem perm_drop_1:
  forall ofs, lo <= ofs < hi -> perm m' b ofs p.
Proof.
  intros.
  unfold drop_perm in DROP. destruct (range_perm_dec m b lo hi p); inv DROP.
  unfold perm. simpl. rewrite update_s. unfold proj_sumbool. 
  rewrite zle_true. rewrite zlt_true. simpl. constructor.
  omega. omega. 
Qed.
  
Theorem perm_drop_2:
  forall ofs p', lo <= ofs < hi -> perm m' b ofs p' -> perm_order p p'.
Proof.
  intros.
  unfold drop_perm in DROP. destruct (range_perm_dec m b lo hi p); inv DROP.
  revert H0. unfold perm; simpl. rewrite update_s. unfold proj_sumbool. 
  rewrite zle_true. rewrite zlt_true. simpl. auto. 
  omega. omega. 
Qed.

Theorem perm_drop_3:
  forall b' ofs p', b' <> b \/ ofs < lo \/ hi <= ofs -> perm m b' ofs p' -> perm m' b' ofs p'.
Proof.
  intros.
  unfold drop_perm in DROP. destruct (range_perm_dec m b lo hi p); inv DROP.
  unfold perm; simpl. unfold update. destruct (zeq b' b). subst b'. 
  unfold proj_sumbool. destruct (zle lo ofs). destruct (zlt ofs hi). 
  byContradiction. intuition omega.
  auto. auto. auto.
Qed.

Theorem perm_drop_4:
  forall b' ofs p', perm m' b' ofs p' -> perm m b' ofs p'.
Proof.
  intros.
  unfold drop_perm in DROP. destruct (range_perm_dec m b lo hi p); inv DROP.
  revert H. unfold perm; simpl. unfold update. destruct (zeq b' b). 
  subst b'. unfold proj_sumbool. destruct (zle lo ofs). destruct (zlt ofs hi).
  simpl. intros. apply perm_implies with p. apply r. tauto. auto.
  auto. auto. auto.
Qed.

Theorem bounds_drop:
  forall b', bounds m' b' = bounds m b'.
Proof.
  intros.
  unfold drop_perm in DROP. destruct (range_perm_dec m b lo hi p); inv DROP.
  unfold bounds; simpl. auto.
Qed.

Lemma valid_access_drop_1:
  forall chunk b' ofs p', 
  b' <> b \/ ofs + size_chunk chunk <= lo \/ hi <= ofs \/ perm_order p p' ->
  valid_access m chunk b' ofs p' -> valid_access m' chunk b' ofs p'.
Proof.
  intros. destruct H0. split; auto. 
  red; intros.
  destruct (zeq b' b). subst b'.
  destruct (zlt ofs0 lo). eapply perm_drop_3; eauto. 
  destruct (zle hi ofs0). eapply perm_drop_3; eauto.
  apply perm_implies with p. eapply perm_drop_1; eauto. omega. 
  generalize (size_chunk_pos chunk); intros. intuition. omegaContradiction. omegaContradiction.
  eapply perm_drop_3; eauto.
Qed.

Lemma valid_access_drop_2:
  forall chunk b' ofs p', 
  valid_access m' chunk b' ofs p' -> valid_access m chunk b' ofs p'.
Proof.
  intros. destruct H; split; auto. 
  red; intros. eapply perm_drop_4; eauto. 
Qed.

(*
Lemma valid_access_drop_3:
  forall chunk b' ofs p',
  valid_access m' chunk b' ofs p' ->
  b' <> b \/ Intv.disjoint (lo, hi) (ofs, ofs + size_chunk chunk) \/ perm_order p p'.
Proof.
  intros. destruct H. 
  destruct (zeq b' b); auto. subst b'.
  destruct (Intv.disjoint_dec (lo, hi) (ofs, ofs + size_chunk chunk)); auto. 
  exploit intv_not_disjoint; eauto. intros [x [A B]]. 
  right; right. apply perm_drop_2 with x. auto. apply H. auto. 
Qed.
*)

Theorem load_drop:
  forall chunk b' ofs, 
  b' <> b \/ ofs + size_chunk chunk <= lo \/ hi <= ofs \/ perm_order p Readable ->
  load chunk m' b' ofs = load chunk m b' ofs.
Proof.
  intros.
  unfold load.
  destruct (valid_access_dec m chunk b' ofs Readable).
  rewrite pred_dec_true.
  unfold drop_perm in DROP. destruct (range_perm_dec m b lo hi p); inv DROP. simpl.
  unfold update. destruct (zeq b' b). subst b'. decEq. decEq. 
  apply getN_exten. rewrite <- size_chunk_conv. intros.
  unfold proj_sumbool. destruct (zle lo i). destruct (zlt i hi). destruct (perm_order_dec p Readable).
  auto.
  elimtype False. intuition.
  auto. auto. auto.
  eapply valid_access_drop_1; eauto. 
  rewrite pred_dec_false. auto.
  red; intros; elim n. eapply valid_access_drop_2; eauto.
Qed.

End DROP.

(** * Extensionality properties *)

Lemma mem_access_ext:
  forall m1 m2, perm m1 = perm m2 -> mem_access m1 = mem_access m2.
Proof.
  intros.
  apply extensionality; intro b.
  apply extensionality; intro ofs.
  case_eq (mem_access m1 b ofs); case_eq (mem_access m2 b ofs); intros; auto.
  assert (perm m1 b ofs p <-> perm m2 b ofs p) by (rewrite H; intuition).
  assert (perm m1 b ofs p0 <-> perm m2 b ofs p0) by (rewrite H; intuition).
  unfold perm, perm_order' in H2,H3.
  rewrite H0 in H2,H3; rewrite H1 in H2,H3.
  f_equal.
  assert (perm_order p p0 -> perm_order p0 p -> p0=p) by
    (clear; intros; inv H; inv H0; auto).
  intuition.
  assert (perm m1 b ofs p <-> perm m2 b ofs p) by (rewrite H; intuition).
  unfold perm, perm_order' in H2; rewrite H0 in H2; rewrite H1 in H2.
  assert (perm_order p p) by auto with mem.
  intuition.
  assert (perm m1 b ofs p <-> perm m2 b ofs p) by (rewrite H; intuition).
  unfold perm, perm_order'  in H2; rewrite H0 in H2; rewrite H1 in H2.
  assert (perm_order p p) by auto with mem.
  intuition.
Qed.

Lemma mem_ext': 
  forall m1 m2, 
  mem_access m1 = mem_access m2 ->
  nextblock m1 = nextblock m2 ->
  (forall b, 0 < b < nextblock m1 -> bounds m1 b = bounds m2 b) ->
  (forall b ofs, perm_order' (mem_access m1 b ofs) Readable -> 
                          mem_contents m1 b ofs = mem_contents m2 b ofs) ->
  m1 = m2.
Proof.
  intros.
  destruct m1; destruct m2; simpl in *.
  destruct H; subst.
  apply mkmem_ext; auto.
  apply extensionality; intro b.
  apply extensionality; intro ofs.
  destruct (perm_order'_dec (mem_access0 b ofs) Readable).
  auto.
  destruct (noread_undef0 b ofs); try contradiction.
  destruct (noread_undef1 b ofs); try contradiction.
  congruence.
  apply extensionality; intro b.
  destruct (nextblock_noaccess0 b); auto.
  destruct (nextblock_noaccess1 b); auto.
  congruence.
Qed.

Theorem mem_ext:
  forall m1 m2, 
  perm m1 = perm m2 ->
  nextblock m1 = nextblock m2 ->
  (forall b, 0 < b < nextblock m1 -> bounds m1 b = bounds m2 b) ->
  (forall b ofs, loadbytes m1 b ofs 1 = loadbytes m2 b ofs 1) ->
  m1 = m2.
Proof.
  intros.
  generalize (mem_access_ext _ _ H); clear H; intro.
  apply mem_ext'; auto.
  intros.
  specialize (H2 b ofs).
  unfold loadbytes in H2; simpl in H2.
  destruct (range_perm_dec m1 b ofs (ofs+1)).
  destruct (range_perm_dec m2 b ofs (ofs+1)).
  inv H2; auto.
  contradict n.
  intros ofs' ?; assert (ofs'=ofs) by omega; subst ofs'.
  unfold perm, perm_order'.
    rewrite <- H; destruct (mem_access m1 b ofs); try destruct p; intuition.
  contradict n.
  intros ofs' ?; assert (ofs'=ofs) by omega; subst ofs'.
  unfold perm. destruct (mem_access m1 b ofs); try destruct p; intuition.
Qed.

(** * Generic injections *)

(** A memory state [m1] generically injects into another memory state [m2] via the
  memory injection [f] if the following conditions hold:
- each access in [m2] that corresponds to a valid access in [m1]
  is itself valid;
- the memory value associated in [m1] to an accessible address
  must inject into [m2]'s memory value at the corersponding address.
*)

Record mem_inj (f: meminj) (m1 m2: mem) : Prop :=
  mk_mem_inj {
    mi_access:
      forall b1 b2 delta chunk ofs p,
      f b1 = Some(b2, delta) ->
      valid_access m1 chunk b1 ofs p ->
      valid_access m2 chunk b2 (ofs + delta) p;
    mi_memval:
      forall b1 ofs b2 delta,
      f b1 = Some(b2, delta) ->
      perm m1 b1 ofs Nonempty ->
      memval_inject f (m1.(mem_contents) b1 ofs) (m2.(mem_contents) b2 (ofs + delta))
  }.

(** Preservation of permissions *)

Lemma perm_inj:
  forall f m1 m2 b1 ofs p b2 delta,
  mem_inj f m1 m2 ->
  perm m1 b1 ofs p ->
  f b1 = Some(b2, delta) ->
  perm m2 b2 (ofs + delta) p.
Proof.
  intros. 
  assert (valid_access m1 Mint8unsigned b1 ofs p).
    split. red; intros. simpl in H2. replace ofs0 with ofs by omega. auto.
    simpl. apply Zone_divide.
  exploit mi_access; eauto. intros [A B].
  apply A. simpl; omega. 
Qed.

(** Preservation of loads. *)

Lemma getN_inj:
  forall f m1 m2 b1 b2 delta,
  mem_inj f m1 m2 ->
  f b1 = Some(b2, delta) ->
  forall n ofs,
  range_perm m1 b1 ofs (ofs + Z_of_nat n) Readable ->
  list_forall2 (memval_inject f) 
               (getN n ofs (m1.(mem_contents) b1))
               (getN n (ofs + delta) (m2.(mem_contents) b2)).
Proof.
  induction n; intros; simpl.
  constructor.
  rewrite inj_S in H1. 
  constructor. 
  eapply mi_memval; eauto.
  apply perm_implies with Readable.
  apply H1. omega. constructor. 
  replace (ofs + delta + 1) with ((ofs + 1) + delta) by omega.
  apply IHn. red; intros; apply H1; omega. 
Qed.

Lemma load_inj:
  forall f m1 m2 chunk b1 ofs b2 delta v1,
  mem_inj f m1 m2 ->
  load chunk m1 b1 ofs = Some v1 ->
  f b1 = Some (b2, delta) ->
  exists v2, load chunk m2 b2 (ofs + delta) = Some v2 /\ val_inject f v1 v2.
Proof.
  intros.
  exists (decode_val chunk (getN (size_chunk_nat chunk) (ofs + delta) (m2.(mem_contents) b2))).
  split. unfold load. apply pred_dec_true.  
  eapply mi_access; eauto with mem. 
  exploit load_result; eauto. intro. rewrite H2. 
  apply decode_val_inject. apply getN_inj; auto. 
  rewrite <- size_chunk_conv. exploit load_valid_access; eauto. intros [A B]. auto.
Qed.

(** Preservation of stores. *)

Lemma setN_inj:
  forall (access: Z -> Prop) delta f vl1 vl2,
  list_forall2 (memval_inject f) vl1 vl2 ->
  forall p c1 c2,
  (forall q, access q -> memval_inject f (c1 q) (c2 (q + delta))) ->
  (forall q, access q -> memval_inject f ((setN vl1 p c1) q) 
                                         ((setN vl2 (p + delta) c2) (q + delta))).
Proof.
  induction 1; intros; simpl. 
  auto.
  replace (p + delta + 1) with ((p + 1) + delta) by omega.
  apply IHlist_forall2; auto. 
  intros. unfold update at 1. destruct (zeq q0 p). subst q0.
  rewrite update_s. auto.
  rewrite update_o. auto. omega.
Qed.

Definition meminj_no_overlap (f: meminj) (m: mem) : Prop :=
  forall b1 b1' delta1 b2 b2' delta2,
  b1 <> b2 ->
  f b1 = Some (b1', delta1) ->
  f b2 = Some (b2', delta2) ->
  b1' <> b2' 
(*
  \/ low_bound m b1 >= high_bound m b1
  \/ low_bound m b2 >= high_bound m b2 *)
  \/ high_bound m b1 + delta1 <= low_bound m b2 + delta2 
  \/ high_bound m b2 + delta2 <= low_bound m b1 + delta1.

Lemma meminj_no_overlap_perm:
  forall f m b1 b1' delta1 b2 b2' delta2 ofs1 ofs2,
  meminj_no_overlap f m ->
  b1 <> b2 ->
  f b1 = Some (b1', delta1) ->
  f b2 = Some (b2', delta2) ->
  perm m b1 ofs1 Nonempty ->
  perm m b2 ofs2 Nonempty ->
  b1' <> b2' \/ ofs1 + delta1 <> ofs2 + delta2.
Proof.
  intros. exploit H; eauto. intro. 
  exploit perm_in_bounds. eexact H3. intro. 
  exploit perm_in_bounds. eexact H4. intro.
  destruct H5. auto. right. omega. 
Qed.

Lemma store_mapped_inj:
  forall f chunk m1 b1 ofs v1 n1 m2 b2 delta v2,
  mem_inj f m1 m2 ->
  store chunk m1 b1 ofs v1 = Some n1 ->
  meminj_no_overlap f m1 ->
  f b1 = Some (b2, delta) ->
  val_inject f v1 v2 ->
  exists n2,
    store chunk m2 b2 (ofs + delta) v2 = Some n2
    /\ mem_inj f n1 n2.
Proof.
  intros. inversion H. 
  assert (valid_access m2 chunk b2 (ofs + delta) Writable).
    eapply mi_access0; eauto with mem.
  destruct (valid_access_store _ _ _ _ v2 H4) as [n2 STORE]. 
  exists n2; split. eauto.
  constructor.
(* access *)
  intros.
  eapply store_valid_access_1; [apply STORE |].
  eapply mi_access0; eauto.
  eapply store_valid_access_2; [apply H0 |]. auto.
(* mem_contents *)
  intros.
  assert (perm m1 b0 ofs0 Nonempty). eapply perm_store_2; eauto. 
  rewrite (store_mem_contents _ _ _ _ _ _ H0).
  rewrite (store_mem_contents _ _ _ _ _ _ STORE).
  unfold update. 
  destruct (zeq b0 b1). subst b0.
  (* block = b1, block = b2 *)
  assert (b3 = b2) by congruence. subst b3.
  assert (delta0 = delta) by congruence. subst delta0.
  rewrite zeq_true.
  apply setN_inj with (access := fun ofs => perm m1 b1 ofs Nonempty).
  apply encode_val_inject; auto. auto. auto. 
  destruct (zeq b3 b2). subst b3.
  (* block <> b1, block = b2 *)
  rewrite setN_other. auto.
  rewrite encode_val_length. rewrite <- size_chunk_conv. intros. 
  assert (b2 <> b2 \/ ofs0 + delta0 <> (r - delta) + delta).
    eapply meminj_no_overlap_perm; eauto. 
    exploit store_valid_access_3. eexact H0. intros [A B].
    eapply perm_implies. apply A. omega. auto with mem.
  destruct H9. congruence. omega.
  (* block <> b1, block <> b2 *)
  eauto.
Qed.

Lemma store_unmapped_inj:
  forall f chunk m1 b1 ofs v1 n1 m2,
  mem_inj f m1 m2 ->
  store chunk m1 b1 ofs v1 = Some n1 ->
  f b1 = None ->
  mem_inj f n1 m2.
Proof.
  intros. inversion H.
  constructor.
(* access *)
  eauto with mem.
(* mem_contents *)
  intros. 
  rewrite (store_mem_contents _ _ _ _ _ _ H0).
  rewrite update_o. eauto with mem. 
  congruence.
Qed.

Lemma store_outside_inj:
  forall f m1 m2 chunk b ofs v m2',
  mem_inj f m1 m2 ->
  (forall b' delta ofs',
    f b' = Some(b, delta) ->
    perm m1 b' ofs' Nonempty ->
    ofs' + delta < ofs \/ ofs' + delta >= ofs + size_chunk chunk) ->
  store chunk m2 b ofs v = Some m2' ->
  mem_inj f m1 m2'.
Proof.
  intros. inversion H. constructor.
(* access *)
  eauto with mem.
(* mem_contents *)
  intros. 
  rewrite (store_mem_contents _ _ _ _ _ _ H1).
  unfold update. destruct (zeq b2 b). subst b2.
  rewrite setN_outside. auto. 
  rewrite encode_val_length. rewrite <- size_chunk_conv. 
  eapply H0; eauto. 
  eauto with mem.
Qed.

(** Preservation of allocations *)

Lemma alloc_right_inj:
  forall f m1 m2 lo hi b2 m2',
  mem_inj f m1 m2 ->
  alloc m2 lo hi = (m2', b2) ->
  mem_inj f m1 m2'.
Proof.
  intros. injection H0. intros NEXT MEM.
  inversion H. constructor.
(* access *)
  intros. eauto with mem. 
(* mem_contents *)
  intros.
  assert (valid_access m2 Mint8unsigned b0 (ofs + delta) Nonempty).
    eapply mi_access0; eauto.
    split. simpl. red; intros. assert (ofs0 = ofs) by omega. congruence.
    simpl. apply Zone_divide. 
  assert (valid_block m2 b0) by eauto with mem.
  rewrite <- MEM; simpl. rewrite update_o. eauto with mem.
  rewrite NEXT. apply sym_not_equal. eauto with mem. 
Qed.

Lemma alloc_left_unmapped_inj:
  forall f m1 m2 lo hi m1' b1,
  mem_inj f m1 m2 ->
  alloc m1 lo hi = (m1', b1) ->
  f b1 = None ->
  mem_inj f m1' m2.
Proof.
  intros. inversion H. constructor.
(* access *)
  unfold update; intros.
  exploit valid_access_alloc_inv; eauto. unfold eq_block. intros. 
  destruct (zeq b0 b1). congruence. eauto.
(* mem_contents *)
  injection H0; intros NEXT MEM. intros. 
  rewrite <- MEM; simpl. rewrite NEXT. unfold update.
  exploit perm_alloc_inv; eauto. intros. 
  destruct (zeq b0 b1). constructor. eauto.
Qed.

Definition inj_offset_aligned (delta: Z) (size: Z) : Prop :=
  forall chunk, size_chunk chunk <= size -> (align_chunk chunk | delta).

Lemma alloc_left_mapped_inj:
  forall f m1 m2 lo hi m1' b1 b2 delta,
  mem_inj f m1 m2 ->
  alloc m1 lo hi = (m1', b1) ->
  valid_block m2 b2 ->
  inj_offset_aligned delta (hi-lo) ->
  (forall ofs p, lo <= ofs < hi -> perm m2 b2 (ofs + delta) p) ->
  f b1 = Some(b2, delta) ->
  mem_inj f m1' m2.
Proof.
  intros. inversion H. constructor.
(* access *)
  intros. 
  exploit valid_access_alloc_inv; eauto. unfold eq_block. intros.
  destruct (zeq b0 b1). subst b0. rewrite H4 in H5. inversion H5; clear H5; subst b3 delta0.
  split. red; intros. 
  replace ofs0 with ((ofs0 - delta) + delta) by omega. 
  apply H3. omega. 
  destruct H6. apply Zdivide_plus_r. auto. apply H2. omega.
  eauto.
(* mem_contents *)
  injection H0; intros NEXT MEM. 
  intros. rewrite <- MEM; simpl. rewrite NEXT. unfold update.
  exploit perm_alloc_inv; eauto. intros. 
  destruct (zeq b0 b1). constructor. eauto.
Qed.

Lemma free_left_inj:
  forall f m1 m2 b lo hi m1',
  mem_inj f m1 m2 ->
  free m1 b lo hi = Some m1' ->
  mem_inj f m1' m2.
Proof.
  intros. exploit free_result; eauto. intro FREE. inversion H. constructor.
(* access *)
  intros. eauto with mem. 
(* mem_contents *)
  intros. rewrite FREE; simpl.
  assert (b=b1 /\ lo <= ofs < hi \/ (b<>b1 \/ ofs<lo \/ hi <= ofs)) by (unfold block; omega).
  destruct H3.
  destruct H3. subst b1.
  rewrite (clearN_in _ _ _ _ _ H4); auto.
  constructor.
  rewrite (clearN_out _ _ _ _ _ _ H3).
  apply mi_memval0; auto.
  eapply perm_free_3; eauto.
Qed.


Lemma free_right_inj:
  forall f m1 m2 b lo hi m2',
  mem_inj f m1 m2 ->
  free m2 b lo hi = Some m2' ->
  (forall b1 delta ofs p,
    f b1 = Some(b, delta) -> perm m1 b1 ofs p ->
    lo <= ofs + delta < hi -> False) ->
  mem_inj f m1 m2'.
Proof.
  intros. exploit free_result; eauto. intro FREE. inversion H. constructor.
(* access *)
  intros. exploit mi_access0; eauto. intros [RG AL]. split; auto.
  red; intros. eapply perm_free_1; eauto. 
  destruct (zeq b2 b); auto. subst b. right.
  destruct (zlt ofs0 lo); auto. destruct (zle hi ofs0); auto.
  elimtype False. eapply H1 with (ofs := ofs0 - delta). eauto. 
  apply H3. omega. omega.
(* mem_contents *)
  intros. rewrite FREE; simpl.
  specialize (mi_memval0 _ _ _ _ H2 H3).
  assert (b=b2 /\ lo <= ofs+delta < hi \/ (b<>b2 \/ ofs+delta<lo \/ hi <= ofs+delta)) by (unfold block; omega).
  destruct H4. destruct H4. subst b2.
  specialize (H1 _ _ _ _ H2 H3). elimtype False; auto.
  rewrite (clearN_out _ _ _ _ _ _ H4); auto.
Qed.

(** Preservation of [drop_perm] operations. *)

Lemma drop_unmapped_inj:
  forall f m1 m2 b lo hi p m1',
  mem_inj f m1 m2 ->
  drop_perm m1 b lo hi p = Some m1' ->
  f b = None ->
  mem_inj f m1' m2.
Proof.
  intros. inv H. constructor. 
  intros. eapply mi_access0. eauto.
  eapply valid_access_drop_2; eauto. 
  intros. replace (mem_contents m1' b1 ofs) with (mem_contents m1 b1 ofs). 
  apply mi_memval0; auto. 
  eapply perm_drop_4; eauto. 
  unfold drop_perm in H0. destruct (range_perm_dec m1 b lo hi p); inv H0. 
  simpl. rewrite update_o; auto. congruence.
Qed.

Lemma drop_mapped_inj:
  forall f m1 m2 b1 b2 delta lo hi p m1',
  mem_inj f m1 m2 ->
  drop_perm m1 b1 lo hi p = Some m1' ->
  meminj_no_overlap f m1 ->
  f b1 = Some(b2, delta) ->
  exists m2',
      drop_perm m2 b2 (lo + delta) (hi + delta) p = Some m2'
   /\ mem_inj f m1' m2'.
Proof.
  intros. 
  assert ({ m2' | drop_perm m2 b2 (lo + delta) (hi + delta) p = Some m2' }).
  apply range_perm_drop_2. red; intros. 
  replace ofs with ((ofs - delta) + delta) by omega.
  eapply perm_inj; eauto. eapply range_perm_drop_1; eauto. omega. 
  destruct X as [m2' DROP]. exists m2'; split; auto.
  inv H. constructor; intros.
(* access *)
  exploit mi_access0; eauto. eapply valid_access_drop_2; eauto.
  intros [A B]. split; auto. red; intros.
  destruct (eq_block b1 b0). subst b0. rewrite H2 in H; inv H.
  (* b1 = b0 *)
  destruct (zlt ofs0 (lo + delta0)). eapply perm_drop_3; eauto. 
  destruct (zle (hi + delta0) ofs0). eapply perm_drop_3; eauto.
  destruct H3 as [C D].
  assert (perm_order p p0).
    eapply perm_drop_2. eexact H0. instantiate (1 := ofs0 - delta0). omega. 
    apply C. omega. 
  apply perm_implies with p; auto.
  eapply perm_drop_1. eauto. omega.
  (* b1 <> b0 *)
  eapply perm_drop_3; eauto.
  exploit H1; eauto. intros [P | P]. auto. right. 
  destruct (zlt lo hi). 
  exploit range_perm_in_bounds. eapply range_perm_drop_1. eexact H0. auto. 
  intros [U V].
  exploit valid_access_drop_2. eexact H0. eauto.
  intros [C D].
  exploit range_perm_in_bounds. eexact C. generalize (size_chunk_pos chunk); omega. 
  intros [X Y].
  generalize (size_chunk_pos chunk). omega.
  omega.
(* memval *)
  assert (A: perm m1 b0 ofs Nonempty). eapply perm_drop_4; eauto.
  exploit mi_memval0; eauto. intros B.
  unfold drop_perm in *. 
  destruct (range_perm_dec m1 b1 lo hi p); inversion H0; clear H0. clear H5.
  destruct (range_perm_dec m2 b2 (lo + delta) (hi + delta) p); inversion DROP; clear DROP. clear H4.
  simpl. unfold update. destruct (zeq b0 b1). 
  (* b1 = b0 *)
  subst b0. rewrite H2 in H; inv H. rewrite zeq_true. unfold proj_sumbool. 
  destruct (zle lo ofs).
  rewrite zle_true. 
  destruct (zlt ofs hi).
  rewrite zlt_true.
  destruct (perm_order_dec p Readable).
  simpl. auto.
  simpl. constructor.
  omega.
  rewrite zlt_false. simpl. auto. omega. 
  omega.
  rewrite zle_false. simpl. auto. omega.
  (* b1 <> b0 *)
  destruct (zeq b3 b2).
  (* b2 = b3 *)
  subst b3. exploit H1. eauto. eauto. eauto. intros [P | P]. congruence.
  exploit perm_in_bounds; eauto. intros X.
  destruct (zle (lo + delta) (ofs + delta0)).
  destruct (zlt (ofs + delta0) (hi + delta)).
  destruct (zlt lo hi). 
  exploit range_perm_in_bounds. eexact r. auto. intros [Y Z].
  omegaContradiction.
  omegaContradiction.
  simpl. auto.
  simpl. auto.
  auto.
Qed.

(** * Memory extensions *)

(**  A store [m2] extends a store [m1] if [m2] can be obtained from [m1]
  by increasing the sizes of the memory blocks of [m1] (decreasing
  the low bounds, increasing the high bounds), and replacing some of
  the [Vundef] values stored in [m1] by more defined values stored
  in [m2] at the same locations. *)

Record extends' (m1 m2: mem) : Prop :=
  mk_extends {
    mext_next: nextblock m1 = nextblock m2;
    mext_inj:  mem_inj inject_id m1 m2
(*
    mext_bounds: forall b, low_bound m2 b <= low_bound m1 b /\ high_bound m1 b <= high_bound m2 b
*)
  }.

Definition extends := extends'.

Theorem extends_refl:
  forall m, extends m m.
Proof.
  intros. constructor. auto. constructor.
  intros. unfold inject_id in H; inv H. replace (ofs + 0) with ofs by omega. auto.
  intros. unfold inject_id in H; inv H. replace (ofs + 0) with ofs by omega. 
  apply memval_inject_id.
(*  intros. omega. *)
Qed.

Theorem load_extends:
  forall chunk m1 m2 b ofs v1,
  extends m1 m2 ->
  load chunk m1 b ofs = Some v1 ->
  exists v2, load chunk m2 b ofs = Some v2 /\ Val.lessdef v1 v2.
Proof.
  intros. inv H. exploit load_inj; eauto. unfold inject_id; reflexivity. 
  intros [v2 [A B]]. exists v2; split.
  replace (ofs + 0) with ofs in A by omega. auto.
  rewrite val_inject_id in B. auto.
Qed.

Theorem loadv_extends:
  forall chunk m1 m2 addr1 addr2 v1,
  extends m1 m2 ->
  loadv chunk m1 addr1 = Some v1 ->
  Val.lessdef addr1 addr2 ->
  exists v2, loadv chunk m2 addr2 = Some v2 /\ Val.lessdef v1 v2.
Proof.
  unfold loadv; intros. inv H1. 
  destruct addr2; try congruence. eapply load_extends; eauto. 
  congruence.
Qed.

Theorem store_within_extends:
  forall chunk m1 m2 b ofs v1 m1' v2,
  extends m1 m2 ->
  store chunk m1 b ofs v1 = Some m1' ->
  Val.lessdef v1 v2 ->
  exists m2',
     store chunk m2 b ofs v2 = Some m2'
  /\ extends m1' m2'.
Proof.
  intros. inversion H.
  exploit store_mapped_inj; eauto. 
    unfold inject_id; red; intros. inv H3; inv H4. auto.
    unfold inject_id; reflexivity.
    rewrite val_inject_id. eauto.
  intros [m2' [A B]].
  exists m2'; split.
  replace (ofs + 0) with ofs in A by omega. auto.
  split; auto.
  rewrite (nextblock_store _ _ _ _ _ _ H0).
  rewrite (nextblock_store _ _ _ _ _ _ A).
  auto.
(*
  intros.
  rewrite (bounds_store _ _ _ _ _ _ H0).
  rewrite (bounds_store _ _ _ _ _ _ A).
  auto.
*)
Qed.

Theorem store_outside_extends:
  forall chunk m1 m2 b ofs v m2',
  extends m1 m2 ->
  store chunk m2 b ofs v = Some m2' ->
  ofs + size_chunk chunk <= low_bound m1 b \/ high_bound m1 b <= ofs ->
  extends m1 m2'.
Proof.
  intros. inversion H. constructor.
  rewrite (nextblock_store _ _ _ _ _ _ H0). auto.
  eapply store_outside_inj; eauto.
  unfold inject_id; intros. inv H2.
  exploit perm_in_bounds; eauto. omega.
(* 
  intros.
  rewrite (bounds_store _ _ _ _ _ _ H0). auto.
*)
Qed.

Theorem storev_extends:
  forall chunk m1 m2 addr1 v1 m1' addr2 v2,
  extends m1 m2 ->
  storev chunk m1 addr1 v1 = Some m1' ->
  Val.lessdef addr1 addr2 ->
  Val.lessdef v1 v2 ->
  exists m2',
     storev chunk m2 addr2 v2 = Some m2'
  /\ extends m1' m2'.
Proof.
  unfold storev; intros. inv H1. 
  destruct addr2; try congruence. eapply store_within_extends; eauto. 
  congruence.
Qed.

Theorem alloc_extends:
  forall m1 m2 lo1 hi1 b m1' lo2 hi2,
  extends m1 m2 ->
  alloc m1 lo1 hi1 = (m1', b) ->
  lo2 <= lo1 -> hi1 <= hi2 ->
  exists m2',
     alloc m2 lo2 hi2 = (m2', b)
  /\ extends m1' m2'.
Proof.
  intros. inv H. 
  case_eq (alloc m2 lo2 hi2); intros m2' b' ALLOC. 
  assert (b' = b).
    rewrite (alloc_result _ _ _ _ _ H0). 
    rewrite (alloc_result _ _ _ _ _ ALLOC).
    auto.
  subst b'.
  exists m2'; split; auto.
  constructor. 
  rewrite (nextblock_alloc _ _ _ _ _ H0).
  rewrite (nextblock_alloc _ _ _ _ _ ALLOC). 
  congruence.
  eapply alloc_left_mapped_inj with (m1 := m1) (m2 := m2') (b2 := b) (delta := 0); eauto.
  eapply alloc_right_inj; eauto.
  eauto with mem.
  red. intros. apply Zdivide_0.
  intros.
  eapply perm_implies with Freeable; auto with mem.
  eapply perm_alloc_2; eauto.
  omega.
Qed.

Theorem free_left_extends:
  forall m1 m2 b lo hi m1',
  extends m1 m2 ->
  free m1 b lo hi = Some m1' ->
  extends m1' m2.
Proof.
  intros. inv H. constructor.
  rewrite (nextblock_free _ _ _ _ _ H0). auto.
  eapply free_left_inj; eauto.
(*
  intros. rewrite (bounds_free _ _ _ _ _ H0). auto.
*)
Qed.

Theorem free_right_extends:
  forall m1 m2 b lo hi m2',
  extends m1 m2 ->
  free m2 b lo hi = Some m2' ->
  (forall ofs p, lo <= ofs < hi -> ~perm m1 b ofs p) ->
  extends m1 m2'.
Proof.
  intros. inv H. constructor.
  rewrite (nextblock_free _ _ _ _ _ H0). auto.
  eapply free_right_inj; eauto.
  unfold inject_id; intros. inv H.
  elim (H1 ofs p); auto. omega.
(* 
  intros. rewrite (bounds_free _ _ _ _ _ H0). auto.
*)
Qed. 

Theorem free_parallel_extends:
  forall m1 m2 b lo hi m1',
  extends m1 m2 ->
  free m1 b lo hi = Some m1' ->
  exists m2',
     free m2 b lo hi = Some m2'
  /\ extends m1' m2'.
Proof.
  intros. inversion H. 
  assert ({ m2': mem | free m2 b lo hi = Some m2' }).
    apply range_perm_free. red; intros. 
    replace ofs with (ofs + 0) by omega.
    eapply perm_inj with (b1 := b); eauto.
    eapply free_range_perm; eauto.
  destruct X as [m2' FREE]. exists m2'; split; auto.
  inv H. constructor.
  rewrite (nextblock_free _ _ _ _ _ H0).
  rewrite (nextblock_free _ _ _ _ _ FREE). auto.
  eapply free_right_inj with (m1 := m1'); eauto. 
  eapply free_left_inj; eauto. 
  unfold inject_id; intros. inv H. 
  assert (~perm m1' b ofs p). eapply perm_free_2; eauto. omega. 
  contradiction.
(*
  intros.
  rewrite (bounds_free _ _ _ _ _ H0).
  rewrite (bounds_free _ _ _ _ _ FREE).
  auto.
*)
Qed.

Theorem valid_block_extends:
  forall m1 m2 b,
  extends m1 m2 ->
  (valid_block m1 b <-> valid_block m2 b).
Proof.
  intros. inv H. unfold valid_block. rewrite mext_next0. omega. 
Qed.

Theorem perm_extends:
  forall m1 m2 b ofs p,
  extends m1 m2 -> perm m1 b ofs p -> perm m2 b ofs p.
Proof.
  intros. inv H. replace ofs with (ofs + 0) by omega. 
  eapply perm_inj; eauto. 
Qed.

Theorem valid_access_extends:
  forall m1 m2 chunk b ofs p,
  extends m1 m2 -> valid_access m1 chunk b ofs p -> valid_access m2 chunk b ofs p.
Proof.
  intros. inv H. replace ofs with (ofs + 0) by omega. 
  eapply mi_access; eauto. auto. 
Qed.

(*
Theorem bounds_extends:
  forall m1 m2 b,
  extends m1 m2 -> low_bound m2 b <= low_bound m1 b /\ high_bound m1 b <= high_bound m2 b.
Proof.
  intros. inv H. auto.
Qed.
*)

(** * Memory injections *)

(** A memory state [m1] injects into another memory state [m2] via the
  memory injection [f] if the following conditions hold:
- each access in [m2] that corresponds to a valid access in [m1]
  is itself valid;
- the memory value associated in [m1] to an accessible address
  must inject into [m2]'s memory value at the corersponding address;
- unallocated blocks in [m1] must be mapped to [None] by [f];
- if [f b = Some(b', delta)], [b'] must be valid in [m2];
- distinct blocks in [m1] are mapped to non-overlapping sub-blocks in [m2];
- the sizes of [m2]'s blocks are representable with signed machine integers;
- the offsets [delta] are representable with signed machine integers.
*)

Record inject' (f: meminj) (m1 m2: mem) : Prop :=
  mk_inject {
    mi_inj:
      mem_inj f m1 m2;
    mi_freeblocks:
      forall b, ~(valid_block m1 b) -> f b = None;
    mi_mappedblocks:
      forall b b' delta, f b = Some(b', delta) -> valid_block m2 b';
    mi_no_overlap:
      meminj_no_overlap f m1;
    mi_range_offset:
      forall b b' delta,
      f b = Some(b', delta) ->
      Int.min_signed <= delta <= Int.max_signed;
    mi_range_block:
      forall b b' delta,
      f b = Some(b', delta) ->
      delta = 0 \/ 
      (Int.min_signed <= low_bound m2 b' /\ high_bound m2 b' <= Int.max_signed)
  }.

Definition inject := inject'.

Hint Local Resolve mi_mappedblocks mi_range_offset: mem.

(** Preservation of access validity and pointer validity *)

Theorem valid_block_inject_1:
  forall f m1 m2 b1 b2 delta,
  f b1 = Some(b2, delta) ->
  inject f m1 m2 ->
  valid_block m1 b1.
Proof.
  intros. inv H. destruct (zlt b1 (nextblock m1)). auto. 
  assert (f b1 = None). eapply mi_freeblocks; eauto. congruence.
Qed.

Theorem valid_block_inject_2:
  forall f m1 m2 b1 b2 delta,
  f b1 = Some(b2, delta) ->
  inject f m1 m2 ->
  valid_block m2 b2.
Proof.
  intros. eapply mi_mappedblocks; eauto. 
Qed.

Hint Local Resolve valid_block_inject_1 valid_block_inject_2: mem.

Theorem perm_inject:
  forall f m1 m2 b1 b2 delta ofs p,
  f b1 = Some(b2, delta) ->
  inject f m1 m2 ->
  perm m1 b1 ofs p -> perm m2 b2 (ofs + delta) p.
Proof.
  intros. inv H0. eapply perm_inj; eauto. 
Qed.

Theorem valid_access_inject:
  forall f m1 m2 chunk b1 ofs b2 delta p,
  f b1 = Some(b2, delta) ->
  inject f m1 m2 ->
  valid_access m1 chunk b1 ofs p ->
  valid_access m2 chunk b2 (ofs + delta) p.
Proof.
  intros. eapply mi_access; eauto. apply mi_inj; auto. 
Qed.

Theorem valid_pointer_inject:
  forall f m1 m2 b1 ofs b2 delta,
  f b1 = Some(b2, delta) ->
  inject f m1 m2 ->
  valid_pointer m1 b1 ofs = true ->
  valid_pointer m2 b2 (ofs + delta) = true.
Proof.
  intros. 
  rewrite valid_pointer_valid_access in H1.
  rewrite valid_pointer_valid_access.
  eapply valid_access_inject; eauto.
Qed.

(** The following lemmas establish the absence of machine integer overflow
  during address computations. *)

Lemma address_inject:
  forall f m1 m2 b1 ofs1 b2 delta,
  inject f m1 m2 ->
  perm m1 b1 (Int.signed ofs1) Nonempty ->
  f b1 = Some (b2, delta) ->
  Int.signed (Int.add ofs1 (Int.repr delta)) = Int.signed ofs1 + delta.
Proof.
  intros.
  exploit perm_inject; eauto. intro A.
  exploit perm_in_bounds. eexact A. intros [B C]. 
  exploit mi_range_block; eauto. intros [D | [E F]].
  subst delta. rewrite Int.add_zero. omega.
  rewrite Int.add_signed.
  repeat rewrite Int.signed_repr. auto.
  eapply mi_range_offset; eauto.
  omega. 
  eapply mi_range_offset; eauto.
Qed.

Lemma address_inject':
  forall f m1 m2 chunk b1 ofs1 b2 delta,
  inject f m1 m2 ->
  valid_access m1 chunk b1 (Int.signed ofs1) Nonempty ->
  f b1 = Some (b2, delta) ->
  Int.signed (Int.add ofs1 (Int.repr delta)) = Int.signed ofs1 + delta.
Proof.
  intros. destruct H0. eapply address_inject; eauto. 
  apply H0. generalize (size_chunk_pos chunk). omega. 
Qed.

Theorem valid_pointer_inject_no_overflow:
  forall f m1 m2 b ofs b' x,
  inject f m1 m2 ->
  valid_pointer m1 b (Int.signed ofs) = true ->
  f b = Some(b', x) ->
  Int.min_signed <= Int.signed ofs + Int.signed (Int.repr x) <= Int.max_signed.
Proof.
  intros. rewrite valid_pointer_valid_access in H0.
  exploit address_inject'; eauto. intros.
  rewrite Int.signed_repr; eauto.
  rewrite <- H2. apply Int.signed_range. 
  eapply mi_range_offset; eauto.
Qed.

Theorem valid_pointer_inject_val:
  forall f m1 m2 b ofs b' ofs',
  inject f m1 m2 ->
  valid_pointer m1 b (Int.signed ofs) = true ->
  val_inject f (Vptr b ofs) (Vptr b' ofs') ->
  valid_pointer m2 b' (Int.signed ofs') = true.
Proof.
  intros. inv H1.
  exploit valid_pointer_inject_no_overflow; eauto. intro NOOV.
  rewrite Int.add_signed. rewrite Int.signed_repr; auto.
  rewrite Int.signed_repr.
  eapply valid_pointer_inject; eauto.
  eapply mi_range_offset; eauto.
Qed.

Theorem inject_no_overlap:
  forall f m1 m2 b1 b2 b1' b2' delta1 delta2 ofs1 ofs2,
  inject f m1 m2 ->
  b1 <> b2 ->
  f b1 = Some (b1', delta1) ->
  f b2 = Some (b2', delta2) ->
  perm m1 b1 ofs1 Nonempty ->
  perm m1 b2 ofs2 Nonempty ->
  b1' <> b2' \/ ofs1 + delta1 <> ofs2 + delta2.
Proof.
  intros. inv H. eapply meminj_no_overlap_perm; eauto.
Qed.

Theorem different_pointers_inject:
  forall f m m' b1 ofs1 b2 ofs2 b1' delta1 b2' delta2,
  inject f m m' ->
  b1 <> b2 ->
  valid_pointer m b1 (Int.signed ofs1) = true ->
  valid_pointer m b2 (Int.signed ofs2) = true ->
  f b1 = Some (b1', delta1) ->
  f b2 = Some (b2', delta2) ->
  b1' <> b2' \/
  Int.signed (Int.add ofs1 (Int.repr delta1)) <>
  Int.signed (Int.add ofs2 (Int.repr delta2)).
Proof.
  intros. 
  rewrite valid_pointer_valid_access in H1. 
  rewrite valid_pointer_valid_access in H2. 
  rewrite (address_inject' _ _ _ _ _ _ _ _ H H1 H3). 
  rewrite (address_inject' _ _ _ _ _ _ _ _ H H2 H4). 
  inv H1. simpl in H5. inv H2. simpl in H1.
  eapply meminj_no_overlap_perm. 
  eapply mi_no_overlap; eauto. eauto. eauto. eauto. 
  apply (H5 (Int.signed ofs1)). omega.
  apply (H1 (Int.signed ofs2)). omega.
Qed.

(** Preservation of loads *)

Theorem load_inject:
  forall f m1 m2 chunk b1 ofs b2 delta v1,
  inject f m1 m2 ->
  load chunk m1 b1 ofs = Some v1 ->
  f b1 = Some (b2, delta) ->
  exists v2, load chunk m2 b2 (ofs + delta) = Some v2 /\ val_inject f v1 v2.
Proof.
  intros. inv H. eapply load_inj; eauto. 
Qed.

Theorem loadv_inject:
  forall f m1 m2 chunk a1 a2 v1,
  inject f m1 m2 ->
  loadv chunk m1 a1 = Some v1 ->
  val_inject f a1 a2 ->
  exists v2, loadv chunk m2 a2 = Some v2 /\ val_inject f v1 v2.
Proof.
  intros. inv H1; simpl in H0; try discriminate.
  exploit load_inject; eauto. intros [v2 [LOAD INJ]].
  exists v2; split; auto. simpl.
  replace (Int.signed (Int.add ofs1 (Int.repr delta)))
     with (Int.signed ofs1 + delta).
  auto. symmetry. eapply address_inject'; eauto with mem.
Qed.

(** Preservation of stores *)

Theorem store_mapped_inject:
  forall f chunk m1 b1 ofs v1 n1 m2 b2 delta v2,
  inject f m1 m2 ->
  store chunk m1 b1 ofs v1 = Some n1 ->
  f b1 = Some (b2, delta) ->
  val_inject f v1 v2 ->
  exists n2,
    store chunk m2 b2 (ofs + delta) v2 = Some n2
    /\ inject f n1 n2.
Proof.
  intros. inversion H.
  exploit store_mapped_inj; eauto. intros [n2 [STORE MI]].
  exists n2; split. eauto. constructor.
(* inj *)
  auto.
(* freeblocks *)
  eauto with mem. 
(* mappedblocks *)
  eauto with mem.
(* no overlap *)
  red; intros.
  repeat rewrite (bounds_store _ _ _ _ _ _ H0).
  eauto. 
(* range offset *)
  eauto.
(* range blocks *)
  intros. rewrite (bounds_store _ _ _ _ _ _ STORE). eauto.
Qed.

Theorem store_unmapped_inject:
  forall f chunk m1 b1 ofs v1 n1 m2,
  inject f m1 m2 ->
  store chunk m1 b1 ofs v1 = Some n1 ->
  f b1 = None ->
  inject f n1 m2.
Proof.
  intros. inversion H.
  constructor.
(* inj *)
  eapply store_unmapped_inj; eauto.
(* freeblocks *)
  eauto with mem. 
(* mappedblocks *)
  eauto with mem.
(* no overlap *)
  red; intros. 
  repeat rewrite (bounds_store _ _ _ _ _ _ H0).
  eauto. 
(* range offset *)
  eauto.
(* range blocks *)
  auto.
Qed.

Theorem store_outside_inject:
  forall f m1 m2 chunk b ofs v m2',
  inject f m1 m2 ->
  (forall b' delta,
    f b' = Some(b, delta) ->
    high_bound m1 b' + delta <= ofs
    \/ ofs + size_chunk chunk <= low_bound m1 b' + delta) ->
  store chunk m2 b ofs v = Some m2' ->
  inject f m1 m2'.
Proof.
  intros. inversion H. constructor.
(* inj *)
  eapply store_outside_inj; eauto.
  intros. exploit perm_in_bounds; eauto. intro. 
  exploit H0; eauto. intro. omega. 
(* freeblocks *)
  auto.
(* mappedblocks *)
  eauto with mem.
(* no overlap *)
  auto.
(* range offset *)
  auto.
(* rang blocks *)
  intros. rewrite (bounds_store _ _ _ _ _ _ H1). eauto.
Qed.

Theorem storev_mapped_inject:
  forall f chunk m1 a1 v1 n1 m2 a2 v2,
  inject f m1 m2 ->
  storev chunk m1 a1 v1 = Some n1 ->
  val_inject f a1 a2 ->
  val_inject f v1 v2 ->
  exists n2,
    storev chunk m2 a2 v2 = Some n2 /\ inject f n1 n2.
Proof.
  intros. inv H1; simpl in H0; try discriminate.
  simpl. replace (Int.signed (Int.add ofs1 (Int.repr delta)))
            with (Int.signed ofs1 + delta).
  eapply store_mapped_inject; eauto.
  symmetry. eapply address_inject'; eauto with mem.
Qed.

(* Preservation of allocations *)

Theorem alloc_right_inject:
  forall f m1 m2 lo hi b2 m2',
  inject f m1 m2 ->
  alloc m2 lo hi = (m2', b2) ->
  inject f m1 m2'.
Proof.
  intros. injection H0. intros NEXT MEM.
  inversion H. constructor.
(* inj *)
  eapply alloc_right_inj; eauto.
(* freeblocks *)
  auto.
(* mappedblocks *)
  eauto with mem.
(* no overlap *)
  auto.
(* range offset *)
  auto.
(* range block *)
  intros. rewrite (bounds_alloc_other _ _ _ _ _ H0). eauto. 
  eapply valid_not_valid_diff; eauto with mem.
Qed.

Theorem alloc_left_unmapped_inject:
  forall f m1 m2 lo hi m1' b1,
  inject f m1 m2 ->
  alloc m1 lo hi = (m1', b1) ->
  exists f',
     inject f' m1' m2
  /\ inject_incr f f'
  /\ f' b1 = None
  /\ (forall b, b <> b1 -> f' b = f b).
Proof.
  intros. inversion H.
  assert (inject_incr f (update b1 None f)).
    red; unfold update; intros. destruct (zeq b b1). subst b.
    assert (f b1 = None). eauto with mem. congruence.
    auto.
  assert (mem_inj (update b1 None f) m1 m2).
    inversion mi_inj0; constructor; eauto with mem.
    unfold update; intros. destruct (zeq b0 b1). congruence. eauto. 
    unfold update; intros. destruct (zeq b0 b1). congruence. 
    apply memval_inject_incr with f; auto. 
  exists (update b1 None f); split. constructor.
(* inj *)
  eapply alloc_left_unmapped_inj; eauto. apply update_s. 
(* freeblocks *)
  intros. unfold update. destruct (zeq b b1). auto. 
  apply mi_freeblocks0. red; intro; elim H3. eauto with mem. 
(* mappedblocks *)
  unfold update; intros. destruct (zeq b b1). congruence. eauto. 
(* no overlap *)
  unfold update; red; intros.
  destruct (zeq b0 b1); destruct (zeq b2 b1); try congruence.
  repeat rewrite (bounds_alloc_other _ _ _ _ _ H0); eauto.
(* range offset *)
  unfold update; intros.
  destruct (zeq b b1). congruence. eauto.
(* range block *)
  unfold update; intros.
  destruct (zeq b b1). congruence. eauto.
(* incr *)
  split. auto. 
(* image *)
  split. apply update_s.
(* incr *)
  intros; apply update_o; auto.
Qed.

Theorem alloc_left_mapped_inject:
  forall f m1 m2 lo hi m1' b1 b2 delta,
  inject f m1 m2 ->
  alloc m1 lo hi = (m1', b1) ->
  valid_block m2 b2 ->
  Int.min_signed <= delta <= Int.max_signed ->
  delta = 0 \/ Int.min_signed <= low_bound m2 b2 /\ high_bound m2 b2 <= Int.max_signed ->
  (forall ofs p, lo <= ofs < hi -> perm m2 b2 (ofs + delta) p) ->
  inj_offset_aligned delta (hi-lo) ->
  (forall b ofs, 
   f b = Some (b2, ofs) -> 
   high_bound m1 b + ofs <= lo + delta \/
   hi + delta <= low_bound m1 b + ofs) ->
  exists f',
     inject f' m1' m2
  /\ inject_incr f f'
  /\ f' b1 = Some(b2, delta)
  /\ (forall b, b <> b1 -> f' b = f b).
Proof.
  intros. inversion H.
  assert (inject_incr f (update b1 (Some(b2, delta)) f)).
    red; unfold update; intros. destruct (zeq b b1). subst b.
    assert (f b1 = None). eauto with mem. congruence.
    auto.
  assert (mem_inj (update b1 (Some(b2, delta)) f) m1 m2).
    inversion mi_inj0; constructor; eauto with mem.
    unfold update; intros. destruct (zeq b0 b1).
      inv H8. elim (fresh_block_alloc _ _ _ _ _ H0). eauto with mem.
      eauto.
    unfold update; intros. destruct (zeq b0 b1).
      inv H8. elim (fresh_block_alloc _ _ _ _ _ H0). eauto with mem. 
      apply memval_inject_incr with f; auto. 
  exists (update b1 (Some(b2, delta)) f). split. constructor.
(* inj *)
  eapply alloc_left_mapped_inj; eauto. apply update_s.
(* freeblocks *)
  unfold update; intros. destruct (zeq b b1). subst b. 
  elim H9. eauto with mem.
  eauto with mem.
(* mappedblocks *)
  unfold update; intros. destruct (zeq b b1). inv H9. auto.
  eauto.
(* overlap *)
  unfold update; red; intros.
  repeat rewrite (bounds_alloc _ _ _ _ _ H0). unfold eq_block. 
  destruct (zeq b0 b1); destruct (zeq b3 b1); simpl.
  inv H10; inv H11. congruence.
  inv H10. destruct (zeq b1' b2'); auto. subst b2'. 
  right. generalize (H6 _ _ H11). tauto. 
  inv H11. destruct (zeq b1' b2'); auto. subst b2'. 
  right. eapply H6; eauto. 
  eauto.
(* range offset *)
  unfold update; intros. destruct (zeq b b1). inv H9. auto. eauto.
(* range block *)
  unfold update; intros. destruct (zeq b b1). inv H9. auto. eauto.
(* incr *)
  split. auto.
(* image of b1 *)
  split. apply update_s.
(* image of others *)
  intros. apply update_o; auto.
Qed.

Theorem alloc_parallel_inject:
  forall f m1 m2 lo1 hi1 m1' b1 lo2 hi2,
  inject f m1 m2 ->
  alloc m1 lo1 hi1 = (m1', b1) ->
  lo2 <= lo1 -> hi1 <= hi2 ->
  exists f', exists m2', exists b2,
  alloc m2 lo2 hi2 = (m2', b2)
  /\ inject f' m1' m2'
  /\ inject_incr f f'
  /\ f' b1 = Some(b2, 0)
  /\ (forall b, b <> b1 -> f' b = f b).
Proof.
  intros.
  case_eq (alloc m2 lo2 hi2). intros m2' b2 ALLOC.
  exploit alloc_left_mapped_inject. 
  eapply alloc_right_inject; eauto.
  eauto.
  instantiate (1 := b2). eauto with mem.
  instantiate (1 := 0). generalize Int.min_signed_neg Int.max_signed_pos; omega.
  auto.
  intros.
  apply perm_implies with Freeable; auto with mem.
  eapply perm_alloc_2; eauto. omega.
  red; intros. apply Zdivide_0.
  intros. elimtype False. apply (valid_not_valid_diff m2 b2 b2); eauto with mem.
  intros [f' [A [B [C D]]]].
  exists f'; exists m2'; exists b2; auto.
Qed.

(** Preservation of [free] operations *)

Lemma free_left_inject:
  forall f m1 m2 b lo hi m1',
  inject f m1 m2 ->
  free m1 b lo hi = Some m1' ->
  inject f m1' m2.
Proof.
  intros. inversion H. constructor.
(* inj *)
  eapply free_left_inj; eauto.
(* freeblocks *)
  eauto with mem.
(* mappedblocks *)
  auto.
(* no overlap *)
  red; intros. repeat rewrite (bounds_free _ _ _ _ _ H0). eauto. 
(* range offset *)
  auto.
(* range block *)
  auto.
Qed.

Lemma free_list_left_inject:
  forall f m2 l m1 m1',
  inject f m1 m2 ->
  free_list m1 l = Some m1' ->
  inject f m1' m2.
Proof.
  induction l; simpl; intros. 
  inv H0. auto.
  destruct a as [[b lo] hi]. generalize H0. case_eq (free m1 b lo hi); intros.
  apply IHl with m; auto. eapply free_left_inject; eauto.
  congruence.
Qed.

Lemma free_right_inject:
  forall f m1 m2 b lo hi m2',
  inject f m1 m2 ->
  free m2 b lo hi = Some m2' ->
  (forall b1 delta ofs p,
    f b1 = Some(b, delta) -> perm m1 b1 ofs p ->
    lo <= ofs + delta < hi -> False) ->
  inject f m1 m2'.
Proof.
  intros. inversion H. constructor.
(* inj *)
  eapply free_right_inj; eauto.
(* freeblocks *)
  auto.
(* mappedblocks *)
  eauto with mem.
(* no overlap *)
  auto.
(* range offset *)
  auto.
(* range blocks *)
  intros. rewrite (bounds_free _ _ _ _ _ H0). eauto.
Qed.

Lemma perm_free_list:
  forall l m m' b ofs p,
  free_list m l = Some m' ->
  perm m' b ofs p ->
  perm m b ofs p /\ 
  (forall lo hi, In (b, lo, hi) l -> lo <= ofs < hi -> False).
Proof.
  induction l; intros until p; simpl.
  intros. inv H. split; auto. 
  destruct a as [[b1 lo1] hi1].
  case_eq (free m b1 lo1 hi1); intros; try congruence.
  exploit IHl; eauto. intros [A B].
  split. eauto with mem.
  intros. destruct H2. inv H2.
  elim (perm_free_2 _ _ _ _ _ H ofs p). auto. auto.
  eauto.
Qed.

Theorem free_inject:
  forall f m1 l m1' m2 b lo hi m2',
  inject f m1 m2 ->
  free_list m1 l = Some m1' ->
  free m2 b lo hi = Some m2' ->
  (forall b1 delta ofs p,
    f b1 = Some(b, delta) -> 
    perm m1 b1 ofs p -> lo <= ofs + delta < hi ->
    exists lo1, exists hi1, In (b1, lo1, hi1) l /\ lo1 <= ofs < hi1) ->
  inject f m1' m2'.
Proof.
  intros. 
  eapply free_right_inject; eauto. 
  eapply free_list_left_inject; eauto.
  intros. exploit perm_free_list; eauto. intros [A B].
  exploit H2; eauto. intros [lo1 [hi1 [C D]]]. eauto.
Qed.

(*
Theorem free_inject':
  forall f m1 l m1' m2 b lo hi m2',
  inject f m1 m2 ->
  free_list m1 l = Some m1' ->
  free m2 b lo hi = Some m2' ->
  (forall b1 delta,
    f b1 = Some(b, delta) -> In (b1, low_bound m1 b1, high_bound m1 b1) l) ->
  inject f m1' m2'.
Proof.
  intros. eapply free_inject; eauto.
  intros. exists (low_bound m1 b1); exists (high_bound m1 b1).
  split. eauto. apply perm_in_bounds with p. auto.
Qed.
*)

(** Injecting a memory into itself. *)

Definition flat_inj (thr: block) : meminj :=
  fun (b: block) => if zlt b thr then Some(b, 0) else None.

Definition inject_neutral (thr: block) (m: mem) :=
  mem_inj (flat_inj thr) m m.

Remark flat_inj_no_overlap:
  forall thr m, meminj_no_overlap (flat_inj thr) m.
Proof.
  unfold flat_inj; intros; red; intros.
  destruct (zlt b1 thr); inversion H0; subst.
  destruct (zlt b2 thr); inversion H1; subst.
  auto.
Qed.

Theorem neutral_inject:
  forall m, inject_neutral (nextblock m) m -> inject (flat_inj (nextblock m)) m m.
Proof.
  intros. constructor.
(* meminj *)
  auto.
(* freeblocks *)
  unfold flat_inj, valid_block; intros.
  apply zlt_false. omega.
(* mappedblocks *)
  unfold flat_inj, valid_block; intros. 
  destruct (zlt b (nextblock m)); inversion H0; subst. auto.
(* no overlap *)
  apply flat_inj_no_overlap.
(* range *)
  unfold flat_inj; intros.
  destruct (zlt b (nextblock m)); inv H0.
  generalize Int.min_signed_neg Int.max_signed_pos; omega.
(* range *)
  unfold flat_inj; intros.
  destruct (zlt b (nextblock m)); inv H0. auto.
Qed.

Theorem empty_inject_neutral:
  forall thr, inject_neutral thr empty.
Proof.
  intros; red; constructor.
(* access *)
  unfold flat_inj; intros. destruct (zlt b1 thr); inv H.
  replace (ofs + 0) with ofs by omega; auto.
(* mem_contents *)
  intros; simpl; constructor.
Qed.

Theorem alloc_inject_neutral:
  forall thr m lo hi b m',
  alloc m lo hi = (m', b) ->
  inject_neutral thr m ->
  nextblock m < thr ->
  inject_neutral thr m'.
Proof.
  intros; red. 
  eapply alloc_left_mapped_inj with (m1 := m) (b2 := b) (delta := 0). 
  eapply alloc_right_inj; eauto. eauto. eauto with mem. 
  red. intros. apply Zdivide_0. 
  intros.
  apply perm_implies with Freeable; auto with mem.
  eapply perm_alloc_2; eauto. omega. 
  unfold flat_inj. apply zlt_true. 
  rewrite (alloc_result _ _ _ _ _ H). auto.
Qed.

Theorem store_inject_neutral:
  forall chunk m b ofs v m' thr,
  store chunk m b ofs v = Some m' ->
  inject_neutral thr m ->
  b < thr ->
  val_inject (flat_inj thr) v v ->
  inject_neutral thr m'.
Proof.
  intros; red.
  exploit store_mapped_inj. eauto. eauto. apply flat_inj_no_overlap. 
  unfold flat_inj. apply zlt_true; auto. eauto.
  replace (ofs + 0) with ofs by omega.  
  intros [m'' [A B]]. congruence.
Qed. 

Theorem drop_inject_neutral:
  forall m b lo hi p m' thr,
  drop_perm m b lo hi p = Some m' ->
  inject_neutral thr m ->
  b < thr ->
  inject_neutral thr m'.
Proof.
  unfold inject_neutral; intros.
  exploit drop_mapped_inj; eauto. apply flat_inj_no_overlap. 
  unfold flat_inj. apply zlt_true; eauto. 
  repeat rewrite Zplus_0_r. intros [m'' [A B]]. congruence.
Qed.

End Mem.

Notation mem := Mem.mem.

Global Opaque Mem.alloc Mem.free Mem.store Mem.load.

Hint Resolve
  Mem.valid_not_valid_diff
  Mem.perm_implies
  Mem.perm_valid_block
  Mem.range_perm_implies
  Mem.valid_access_implies
  Mem.valid_access_valid_block
  Mem.valid_access_perm
  Mem.valid_access_load
  Mem.load_valid_access
  Mem.valid_access_store
  Mem.perm_store_1
  Mem.perm_store_2
  Mem.nextblock_store
  Mem.store_valid_block_1
  Mem.store_valid_block_2
  Mem.store_valid_access_1
  Mem.store_valid_access_2
  Mem.store_valid_access_3
  Mem.nextblock_alloc
  Mem.alloc_result
  Mem.valid_block_alloc
  Mem.fresh_block_alloc
  Mem.valid_new_block
  Mem.perm_alloc_1
  Mem.perm_alloc_2
  Mem.perm_alloc_3
  Mem.perm_alloc_inv
  Mem.valid_access_alloc_other
  Mem.valid_access_alloc_same
  Mem.valid_access_alloc_inv
  Mem.range_perm_free
  Mem.free_range_perm
  Mem.nextblock_free
  Mem.valid_block_free_1
  Mem.valid_block_free_2
  Mem.perm_free_1
  Mem.perm_free_2
  Mem.perm_free_3
  Mem.valid_access_free_1
  Mem.valid_access_free_2
  Mem.valid_access_free_inv_1
  Mem.valid_access_free_inv_2
: mem.




Require Import Errors.
Require Import Floats.


Notation "s #1" := (fst s) (at level 9, format "s '#1'") : pair_scope.
Notation "s #2" := (snd s) (at level 9, format "s '#2'") : pair_scope.

Local Open Scope pair_scope.
Local Open Scope error_monad_scope.

Set Implicit Arguments.

Module Genv.

(** * Global environments *)

Section GENV.

Variable F: Type.  (**r The type of function descriptions *)
Variable V: Type.  (**r The type of information attached to variables *)

(** The type of global environments. *)

Record t: Type := mkgenv {
  genv_symb: PTree.t block;             (**r mapping symbol -> block *)
  genv_funs: ZMap.t (option F);         (**r mapping function pointer -> definition *)
  genv_vars: ZMap.t (option (globvar V)); (**r mapping variable pointer -> info *)
  genv_nextfun: block;                  (**r next function pointer *)
  genv_nextvar: block;                  (**r next variable pointer *)
  genv_nextfun_neg: genv_nextfun < 0;
  genv_nextvar_pos: genv_nextvar > 0;
  genv_symb_range: forall id b, PTree.get id genv_symb = Some b -> b <> 0 /\ genv_nextfun < b /\ b < genv_nextvar;
  genv_funs_range: forall b f, ZMap.get b genv_funs = Some f -> genv_nextfun < b < 0;
  genv_vars_range: forall b v, ZMap.get b genv_vars = Some v -> 0 < b < genv_nextvar;
  genv_vars_inj: forall id1 id2 b, 
    PTree.get id1 genv_symb = Some b -> PTree.get id2 genv_symb = Some b -> id1 = id2
}.

(** ** Lookup functions *)

(** [find_symbol ge id] returns the block associated with the given name, if any *)

Definition find_symbol (ge: t) (id: ident) : option block :=
  PTree.get id ge.(genv_symb).

(** [find_funct_ptr ge b] returns the function description associated with
    the given address. *)

Definition find_funct_ptr (ge: t) (b: block) : option F :=
  ZMap.get b ge.(genv_funs).

(** [find_funct] is similar to [find_funct_ptr], but the function address
    is given as a value, which must be a pointer with offset 0. *)

Definition find_funct (ge: t) (v: val) : option F :=
  match v with
  | Vptr b ofs => if Int.eq_dec ofs Int.zero then find_funct_ptr ge b else None
  | _ => None
  end.

(** [find_var_info ge b] returns the information attached to the variable
   at address [b]. *)

Definition find_var_info (ge: t) (b: block) : option (globvar V) :=
  ZMap.get b ge.(genv_vars).

(** ** Constructing the global environment *)

Program Definition add_function (ge: t) (idf: ident * F) : t :=
  @mkgenv
    (PTree.set idf#1 ge.(genv_nextfun) ge.(genv_symb))
    (ZMap.set ge.(genv_nextfun) (Some idf#2) ge.(genv_funs))
    ge.(genv_vars)
    (ge.(genv_nextfun) - 1)
    ge.(genv_nextvar)
    _ _ _ _ _ _.
Next Obligation.
  destruct ge; simpl; omega.
Qed.
Next Obligation.
  destruct ge; auto.
Qed.
Next Obligation.
  destruct ge; simpl in *.
  rewrite PTree.gsspec in H. destruct (peq id i). inv H. unfold block; omega.
  exploit genv_symb_range0; eauto. unfold block; omega.
Qed.
Next Obligation.
  destruct ge; simpl in *. rewrite ZMap.gsspec in H. 
  destruct (ZIndexed.eq b genv_nextfun0). subst; omega. 
  exploit genv_funs_range0; eauto. omega.
Qed.
Next Obligation.
  destruct ge; eauto. 
Qed.
Next Obligation.
  destruct ge; simpl in *. 
  rewrite PTree.gsspec in H. rewrite PTree.gsspec in H0. 
  destruct (peq id1 i); destruct (peq id2 i).
  congruence.
  exploit genv_symb_range0; eauto. intros [A B]. inv H. omegaContradiction.
  exploit genv_symb_range0; eauto. intros [A B]. inv H0. omegaContradiction.
  eauto.
Qed.

Program Definition add_variable (ge: t) (idv: ident * globvar V) : t :=
  @mkgenv
    (PTree.set idv#1 ge.(genv_nextvar) ge.(genv_symb))
    ge.(genv_funs)
    (ZMap.set ge.(genv_nextvar) (Some idv#2) ge.(genv_vars))
    ge.(genv_nextfun)
    (ge.(genv_nextvar) + 1)
    _ _ _ _ _ _.
Next Obligation.
  destruct ge; auto.
Qed.
Next Obligation.
  destruct ge; simpl; omega.
Qed.
Next Obligation.
  destruct ge; simpl in *.
  rewrite PTree.gsspec in H. destruct (peq id i). inv H. unfold block; omega.
  exploit genv_symb_range0; eauto. unfold block; omega.
Qed.
Next Obligation.
  destruct ge; eauto. 
Qed.
Next Obligation.
  destruct ge; simpl in *. rewrite ZMap.gsspec in H. 
  destruct (ZIndexed.eq b genv_nextvar0). subst; omega. 
  exploit genv_vars_range0; eauto. omega.
Qed.
Next Obligation.
  destruct ge; simpl in *. 
  rewrite PTree.gsspec in H. rewrite PTree.gsspec in H0. 
  destruct (peq id1 i); destruct (peq id2 i).
  congruence.
  exploit genv_symb_range0; eauto. intros [A B]. inv H. omegaContradiction.
  exploit genv_symb_range0; eauto. intros [A B]. inv H0. omegaContradiction.
  eauto.
Qed.

Program Definition empty_genv : t :=
  @mkgenv (PTree.empty block) (ZMap.init None) (ZMap.init None) (-1) 1 _ _ _ _ _ _.
Next Obligation.
  omega.
Qed.
Next Obligation.
  omega.
Qed.
Next Obligation.
  rewrite PTree.gempty in H. discriminate.
Qed.
Next Obligation.
  rewrite ZMap.gi in H. discriminate.
Qed.
Next Obligation.
  rewrite ZMap.gi in H. discriminate.
Qed.
Next Obligation.
  rewrite PTree.gempty in H. discriminate.
Qed.

Definition add_functions (ge: t) (fl: list (ident * F)) : t :=
  List.fold_left add_function fl ge.

Definition add_variables (ge: t) (vl: list (ident * globvar V)) : t :=
  List.fold_left add_variable vl ge.

Definition globalenv (p: AST.program F V) :=
  add_variables (add_functions empty_genv p.(prog_funct)) p.(prog_vars).

(** ** Properties of the operations over global environments *)

Theorem find_funct_inv:
  forall ge v f,
  find_funct ge v = Some f -> exists b, v = Vptr b Int.zero.
Proof.
  intros until f; unfold find_funct. 
  destruct v; try congruence. 
  destruct (Int.eq_dec i Int.zero); try congruence.
  intros. exists b; congruence.
Qed.

Theorem find_funct_find_funct_ptr:
  forall ge b,
  find_funct ge (Vptr b Int.zero) = find_funct_ptr ge b.
Proof.
  intros; simpl. apply dec_eq_true.
Qed.

Theorem find_symbol_exists:
  forall p id gv,
  In (id, gv) (prog_vars p) ->
  exists b, find_symbol (globalenv p) id = Some b.
Proof.
  intros until gv.
  assert (forall vl ge,
          (exists b, find_symbol ge id = Some b) ->
          exists b, find_symbol (add_variables ge vl) id = Some b).
  unfold find_symbol; induction vl; simpl; intros. auto. apply IHvl.
  simpl. rewrite PTree.gsspec. fold ident. destruct (peq id a#1).
  exists (genv_nextvar ge); auto. auto.

  assert (forall vl ge, In (id, gv) vl ->
          exists b, find_symbol (add_variables ge vl) id = Some b).
  unfold find_symbol; induction vl; simpl; intros. contradiction.
  destruct H0. apply H. subst; unfold find_symbol; simpl.
  rewrite PTree.gss. exists (genv_nextvar ge); auto.
  eauto.

  intros. unfold globalenv; eauto. 
Qed.

Remark add_functions_same_symb:
  forall id fl ge, 
  ~In id (map (@fst ident F) fl) ->
  find_symbol (add_functions ge fl) id = find_symbol ge id.
Proof.
  induction fl; simpl; intros. auto. 
  rewrite IHfl. unfold find_symbol; simpl. apply PTree.gso. intuition. intuition.
Qed.

Remark add_functions_same_address:
  forall b fl ge,
  b > ge.(genv_nextfun) ->
  find_funct_ptr (add_functions ge fl) b = find_funct_ptr ge b.
Proof.
  induction fl; simpl; intros. auto. 
  rewrite IHfl. unfold find_funct_ptr; simpl. apply ZMap.gso. 
  red; intros; subst b; omegaContradiction.
  simpl. omega. 
Qed.

Remark add_variables_same_symb:
  forall id vl ge, 
  ~In id (map (@fst ident (globvar V)) vl) ->
  find_symbol (add_variables ge vl) id = find_symbol ge id.
Proof.
  induction vl; simpl; intros. auto. 
  rewrite IHvl. unfold find_symbol; simpl. apply PTree.gso. intuition. intuition.
Qed.

Remark add_variables_same_address:
  forall b vl ge,
  b < ge.(genv_nextvar) ->
  find_var_info (add_variables ge vl) b = find_var_info ge b.
Proof.
  induction vl; simpl; intros. auto. 
  rewrite IHvl. unfold find_var_info; simpl. apply ZMap.gso. 
  red; intros; subst b; omegaContradiction.
  simpl. omega. 
Qed.

Remark add_variables_same_funs:
  forall b vl ge, find_funct_ptr (add_variables ge vl) b = find_funct_ptr ge b.
Proof.
  induction vl; simpl; intros. auto. rewrite IHvl. auto.
Qed.

Remark add_functions_nextvar:
  forall fl ge, genv_nextvar (add_functions ge fl) = genv_nextvar ge.
Proof.
  induction fl; simpl; intros. auto. rewrite IHfl. auto. 
Qed.

Remark add_variables_nextvar:
  forall vl ge, genv_nextvar (add_variables ge vl) = genv_nextvar ge + Z_of_nat(List.length vl).
Proof.
  induction vl; intros.
  simpl. unfold block; omega.
  simpl length; rewrite inj_S; simpl. rewrite IHvl. simpl. unfold block; omega.
Qed.

Theorem find_funct_ptr_exists:
  forall p id f,
  list_norepet (prog_funct_names p) ->
  list_disjoint (prog_funct_names p) (prog_var_names p) ->
  In (id, f) (prog_funct p) ->
  exists b, find_symbol (globalenv p) id = Some b
         /\ find_funct_ptr (globalenv p) b = Some f.
Proof.
  intros until f.

  assert (forall fl ge, In (id, f) fl -> list_norepet (map (@fst ident F) fl) ->
          exists b, find_symbol (add_functions ge fl) id = Some b
                 /\ find_funct_ptr (add_functions ge fl) b = Some f).
  induction fl; simpl; intros. contradiction. inv H0. 
  destruct H. subst a. exists (genv_nextfun ge); split.
  rewrite add_functions_same_symb; auto. unfold find_symbol; simpl. apply PTree.gss.
  rewrite add_functions_same_address. unfold find_funct_ptr; simpl. apply ZMap.gss. 
  simpl; omega.
  apply IHfl; auto. 

  intros. exploit (H p.(prog_funct) empty_genv); eauto. intros [b [A B]].
  unfold globalenv; exists b; split.
  rewrite add_variables_same_symb. auto. eapply list_disjoint_notin; eauto. 
  unfold prog_funct_names. change id with (fst (id, f)). apply in_map; auto. 
  rewrite add_variables_same_funs. auto.
Qed.

Theorem find_funct_ptr_prop:
  forall (P: F -> Prop) p b f,
  (forall id f, In (id, f) (prog_funct p) -> P f) ->
  find_funct_ptr (globalenv p) b = Some f ->
  P f.
Proof.
  intros until f. intros PROP.
  assert (forall fl ge,
          List.incl fl (prog_funct p) ->
          match find_funct_ptr ge b with None => True | Some f => P f end ->
          match find_funct_ptr (add_functions ge fl) b with None => True | Some f => P f end).
  induction fl; simpl; intros. auto.
  apply IHfl. eauto with coqlib. unfold find_funct_ptr; simpl.
  destruct a as [id' f']; simpl. 
  rewrite ZMap.gsspec. destruct (ZIndexed.eq b (genv_nextfun ge)). 
  apply PROP with id'. apply H. auto with coqlib. 
  assumption.

  unfold globalenv. rewrite add_variables_same_funs. intro. 
  exploit (H p.(prog_funct) empty_genv). auto with coqlib. 
  unfold find_funct_ptr; simpl. rewrite ZMap.gi. auto.
  rewrite H0. auto.
Qed.

Theorem find_funct_prop:
  forall (P: F -> Prop) p v f,
  (forall id f, In (id, f) (prog_funct p) -> P f) ->
  find_funct (globalenv p) v = Some f ->
  P f.
Proof.
  intros. exploit find_funct_inv; eauto. intros [b EQ]. subst v. 
  rewrite find_funct_find_funct_ptr in H0. 
  eapply find_funct_ptr_prop; eauto.
Qed.

Theorem find_funct_ptr_inversion:
  forall p b f,
  find_funct_ptr (globalenv p) b = Some f ->
  exists id, In (id, f) (prog_funct p).
Proof.
  intros. pattern f. apply find_funct_ptr_prop with p b; auto.
  intros. exists id; auto.
Qed.

Theorem find_funct_inversion:
  forall p v f,
  find_funct (globalenv p) v = Some f ->
  exists id, In (id, f) (prog_funct p).
Proof.
  intros. pattern f. apply find_funct_prop with p v; auto.
  intros. exists id; auto.
Qed.

Theorem find_funct_ptr_negative:
  forall p b f,
  find_funct_ptr (globalenv p) b = Some f -> b < 0.
Proof.
  unfold find_funct_ptr. intros. destruct (globalenv p). simpl in H. 
  exploit genv_funs_range0; eauto. omega. 
Qed.

Theorem find_var_info_positive:
  forall p b v,
  find_var_info (globalenv p) b = Some v -> b > 0.
Proof.
  unfold find_var_info. intros. destruct (globalenv p). simpl in H. 
  exploit genv_vars_range0; eauto. omega. 
Qed.

Remark add_variables_symb_neg:
  forall id b vl ge,
  find_symbol (add_variables ge vl) id = Some b -> b < 0 ->
  find_symbol ge id = Some b.
Proof.
  induction vl; simpl; intros. auto.
  exploit IHvl; eauto. unfold find_symbol; simpl. rewrite PTree.gsspec. 
  fold ident. destruct (peq id (a#1)); auto. intros. inv H1. 
  generalize (genv_nextvar_pos ge). intros. omegaContradiction.
Qed.

Theorem find_funct_ptr_symbol_inversion:
  forall p id b f,
  find_symbol (globalenv p) id = Some b ->
  find_funct_ptr (globalenv p) b = Some f ->
  In (id, f) p.(prog_funct).
Proof.
  intros until f.

  assert (forall fl ge,
          find_symbol (add_functions ge fl) id = Some b ->
          find_funct_ptr (add_functions ge fl) b = Some f ->
          In (id, f) fl \/ (find_symbol ge id = Some b /\ find_funct_ptr ge b = Some f)).
  induction fl; simpl; intros.
  auto.
  exploit IHfl; eauto. intros [A | [A B]]. auto.
  destruct a as [id' f'].
  unfold find_symbol in A; simpl in A.
  unfold find_funct_ptr in B; simpl in B.
  rewrite PTree.gsspec in A. destruct (peq id id'). inv A. 
  rewrite ZMap.gss in B. inv B. auto.
  rewrite ZMap.gso in B. right; auto. 
  exploit genv_symb_range; eauto. unfold block, ZIndexed.t; omega.

  intros. assert (b < 0) by (eapply find_funct_ptr_negative; eauto). 
  unfold globalenv in *. rewrite add_variables_same_funs in H1.
  exploit (H (prog_funct p) empty_genv). 
  eapply add_variables_symb_neg; eauto. auto. 
  intuition. unfold find_symbol in H3; simpl in H3. rewrite PTree.gempty in H3. discriminate.
Qed.

Theorem find_symbol_not_nullptr:
  forall p id b,
  find_symbol (globalenv p) id = Some b -> b <> Mem.nullptr.
Proof.
  intros until b. unfold find_symbol. destruct (globalenv p); simpl. 
  intros. exploit genv_symb_range0; eauto. intuition.
Qed.

Theorem global_addresses_distinct:
  forall ge id1 id2 b1 b2,
  id1 <> id2 ->
  find_symbol ge id1 = Some b1 ->
  find_symbol ge id2 = Some b2 ->
  b1 <> b2.
Proof.
  intros. red; intros; subst. elim H. destruct ge. eauto. 
Qed.

(** * Construction of the initial memory state *)

Section INITMEM.

Variable ge: t.

Definition init_data_size (i: init_data) : Z :=
  match i with
  | Init_int8 _ => 1
  | Init_int16 _ => 2
  | Init_int32 _ => 4
  | Init_float32 _ => 4
  | Init_float64 _ => 8
  | Init_addrof _ _ => 4
  | Init_space n => Zmax n 0
  end.

Lemma init_data_size_pos:
  forall i, init_data_size i >= 0.
Proof.
  destruct i; simpl; try omega. generalize (Zle_max_r z 0). omega.
Qed.

Definition store_init_data (m: mem) (b: block) (p: Z) (id: init_data) : option mem :=
  match id with
  | Init_int8 n => Mem.store Mint8unsigned m b p (Vint n)
  | Init_int16 n => Mem.store Mint16unsigned m b p (Vint n)
  | Init_int32 n => Mem.store Mint32 m b p (Vint n)
  | Init_float32 n => Mem.store Mfloat32 m b p (Vfloat n)
  | Init_float64 n => Mem.store Mfloat64 m b p (Vfloat n)
  | Init_addrof symb ofs =>
      match find_symbol ge symb with
      | None => None
      | Some b' => Mem.store Mint32 m b p (Vptr b' ofs)
      end
  | Init_space n => Some m
  end.

Fixpoint store_init_data_list (m: mem) (b: block) (p: Z) (idl: list init_data)
                              {struct idl}: option mem :=
  match idl with
  | nil => Some m
  | id :: idl' =>
      match store_init_data m b p id with
      | None => None
      | Some m' => store_init_data_list m' b (p + init_data_size id) idl'
      end
  end.

Fixpoint init_data_list_size (il: list init_data) {struct il} : Z :=
  match il with
  | nil => 0
  | i :: il' => init_data_size i + init_data_list_size il'
  end.

Definition perm_globvar (gv: globvar V) : permission :=
  if gv.(gvar_volatile) then Nonempty
  else if gv.(gvar_readonly) then Readable
  else Writable.

Definition alloc_variable (m: mem) (idv: ident * globvar V) : option mem :=
  let init := idv#2.(gvar_init) in
  let (m', b) := Mem.alloc m 0 (init_data_list_size init) in
  match store_init_data_list m' b 0 init with
  | None => None
  | Some m'' => Mem.drop_perm m'' b 0 (init_data_list_size init) (perm_globvar idv#2)
  end.

Fixpoint alloc_variables (m: mem) (vl: list (ident * globvar V))
                         {struct vl} : option mem :=
  match vl with
  | nil => Some m
  | v :: vl' =>
      match alloc_variable m v with
      | None => None
      | Some m' => alloc_variables m' vl'
      end
  end.

Remark store_init_data_list_nextblock:
  forall idl b m p m',
  store_init_data_list m b p idl = Some m' ->
  Mem.nextblock m' = Mem.nextblock m.
Proof.
  induction idl; simpl; intros until m'.
  intros. congruence.
  caseEq (store_init_data m b p a); try congruence. intros. 
  transitivity (Mem.nextblock m0). eauto. 
  destruct a; simpl in H; try (eapply Mem.nextblock_store; eauto; fail).
  congruence. 
  destruct (find_symbol ge i); try congruence. eapply Mem.nextblock_store; eauto. 
Qed.

Remark alloc_variables_nextblock:
  forall vl m m',
  alloc_variables m vl = Some m' ->
  Mem.nextblock m' = Mem.nextblock m + Z_of_nat(List.length vl).
Proof.
  induction vl.
  simpl; intros. inv H; unfold block; omega.
  simpl length; rewrite inj_S; simpl. intros m m'. 
  unfold alloc_variable. 
  set (init := gvar_init a#2).
  caseEq (Mem.alloc m 0 (init_data_list_size init)). intros m1 b ALLOC.
  caseEq (store_init_data_list m1 b 0 init); try congruence. intros m2 STORE.
  caseEq (Mem.drop_perm m2 b 0 (init_data_list_size init) (perm_globvar a#2)); try congruence.
  intros m3 DROP REC.
  rewrite (IHvl _ _ REC).
  rewrite (Mem.nextblock_drop _ _ _ _ _ _ DROP). 
  rewrite (store_init_data_list_nextblock _ _ _ _ STORE).
  rewrite (Mem.nextblock_alloc _ _ _ _ _ ALLOC).
  unfold block in *; omega.
Qed.

Remark store_init_data_list_perm:
  forall prm b' q idl b m p m',
  store_init_data_list m b p idl = Some m' ->
  Mem.perm m b' q prm -> Mem.perm m' b' q prm.
Proof.
  induction idl; simpl; intros until m'.
  intros. congruence.
  caseEq (store_init_data m b p a); try congruence. intros. 
  eapply IHidl; eauto. 
  destruct a; simpl in H; eauto with mem.
  congruence.
  destruct (find_symbol ge i); try congruence. eauto with mem.
Qed.

Remark alloc_variables_perm:
  forall prm b' q vl m m',
  alloc_variables m vl = Some m' ->
  Mem.perm m b' q prm -> Mem.perm m' b' q prm.
Proof.
  induction vl.
  simpl; intros. congruence.
  intros until m'. simpl. unfold alloc_variable. 
  set (init := gvar_init a#2).
  caseEq (Mem.alloc m 0 (init_data_list_size init)). intros m1 b ALLOC.
  caseEq (store_init_data_list m1 b 0 init); try congruence. intros m2 STORE.
  caseEq (Mem.drop_perm m2 b 0 (init_data_list_size init) (perm_globvar a#2)); try congruence.
  intros m3 DROP REC PERM.
  assert (b' <> b). apply Mem.valid_not_valid_diff with m; eauto with mem.
  eapply IHvl; eauto.
  eapply Mem.perm_drop_3; eauto. 
  eapply store_init_data_list_perm; eauto. 
  eauto with mem.
Qed.

Remark store_init_data_list_outside:
  forall b il m p m',
  store_init_data_list m b p il = Some m' ->
  forall chunk b' q,
  b' <> b \/ q + size_chunk chunk <= p ->
  Mem.load chunk m' b' q = Mem.load chunk m b' q.
Proof.
  induction il; simpl.
  intros; congruence.
  intros until m'. caseEq (store_init_data m b p a); try congruence. 
  intros m1 A B chunk b' q C. transitivity (Mem.load chunk m1 b' q).
  eapply IHil; eauto. generalize (init_data_size_pos a). intuition omega.
  destruct a; simpl in A;
  try (eapply Mem.load_store_other; eauto; intuition; fail).
  congruence.
  destruct (find_symbol ge i); try congruence. 
  eapply Mem.load_store_other; eauto; intuition.
Qed.

Fixpoint load_store_init_data (m: mem) (b: block) (p: Z) (il: list init_data) {struct il} : Prop :=
  match il with
  | nil => True
  | Init_int8 n :: il' =>
      Mem.load Mint8unsigned m b p = Some(Vint(Int.zero_ext 8 n))
      /\ load_store_init_data m b (p + 1) il'
  | Init_int16 n :: il' =>
      Mem.load Mint16unsigned m b p = Some(Vint(Int.zero_ext 16 n))
      /\ load_store_init_data m b (p + 2) il'
  | Init_int32 n :: il' =>
      Mem.load Mint32 m b p = Some(Vint n)
      /\ load_store_init_data m b (p + 4) il'
  | Init_float32 n :: il' =>
      Mem.load Mfloat32 m b p = Some(Vfloat(Float.singleoffloat n))
      /\ load_store_init_data m b (p + 4) il'
  | Init_float64 n :: il' =>
      Mem.load Mfloat64 m b p = Some(Vfloat n)
      /\ load_store_init_data m b (p + 8) il'
  | Init_addrof symb ofs :: il' =>
      (exists b', find_symbol ge symb = Some b' /\ Mem.load Mint32 m b p = Some(Vptr b' ofs))
      /\ load_store_init_data m b (p + 4) il'
  | Init_space n :: il' =>
      load_store_init_data m b (p + Zmax n 0) il'
  end.

Lemma store_init_data_list_charact:
  forall b il m p m',
  store_init_data_list m b p il = Some m' ->
  load_store_init_data m' b p il.
Proof.
  assert (A: forall chunk v m b p m1 il m',
    Mem.store chunk m b p v = Some m1 ->
    store_init_data_list m1 b (p + size_chunk chunk) il = Some m' ->
    Val.has_type v (type_of_chunk chunk) ->
    Mem.load chunk m' b p = Some(Val.load_result chunk v)).
  intros. transitivity (Mem.load chunk m1 b p).
  eapply store_init_data_list_outside; eauto. right. omega. 
  eapply Mem.load_store_same; eauto. 

  induction il; simpl.
  auto.
  intros until m'. caseEq (store_init_data m b p a); try congruence. 
  intros m1 B C.
  exploit IHil; eauto. intro D. 
  destruct a; simpl in B; intuition.
  eapply (A Mint8unsigned (Vint i)); eauto. simpl; auto.
  eapply (A Mint16unsigned (Vint i)); eauto. simpl; auto.
  eapply (A Mint32 (Vint i)); eauto. simpl; auto.
  eapply (A Mfloat32 (Vfloat f)); eauto. simpl; auto.
  eapply (A Mfloat64 (Vfloat f)); eauto. simpl; auto.
  destruct (find_symbol ge i); try congruence. exists b0; split; auto. 
  eapply (A Mint32 (Vptr b0 i0)); eauto. simpl; auto. 
Qed.

Remark load_alloc_variables:
  forall chunk b p vl m m',
  alloc_variables m vl = Some m' ->
  Mem.valid_block m b ->
  Mem.load chunk m' b p = Mem.load chunk m b p.
Proof.
  induction vl; simpl; intros until m'.
  congruence.
  unfold alloc_variable. 
  set (init := gvar_init a#2).
  caseEq (Mem.alloc m 0 (init_data_list_size init)); intros m1 b1 ALLOC.
  caseEq (store_init_data_list m1 b1 0 init); try congruence. intros m2 STO.
  caseEq (Mem.drop_perm m2 b1 0 (init_data_list_size init) (perm_globvar a#2)); try congruence.
  intros m3 DROP RED VALID.
  assert (b <> b1). apply Mem.valid_not_valid_diff with m; eauto with mem.
  transitivity (Mem.load chunk m3 b p).
  apply IHvl; auto. red.
  rewrite (Mem.nextblock_drop _ _ _ _ _ _ DROP). 
  rewrite (store_init_data_list_nextblock _ _ _ _ STO).
  change (Mem.valid_block m1 b). eauto with mem.
  transitivity (Mem.load chunk m2 b p). 
  eapply Mem.load_drop; eauto. 
  transitivity (Mem.load chunk m1 b p).
  eapply store_init_data_list_outside; eauto. 
  eapply Mem.load_alloc_unchanged; eauto.
Qed. 

Remark load_store_init_data_invariant:
  forall m m' b,
  (forall chunk ofs, Mem.load chunk m' b ofs = Mem.load chunk m b ofs) ->
  forall il p,
  load_store_init_data m b p il -> load_store_init_data m' b p il.
Proof.
  induction il; intro p; simpl.
  auto.
  repeat rewrite H. destruct a; intuition. 
Qed.

Lemma alloc_variables_charact:
  forall id gv vl g m m',
  genv_nextvar g = Mem.nextblock m ->
  alloc_variables m vl = Some m' ->
  list_norepet (map (@fst ident (globvar V)) vl) ->
  In (id, gv) vl ->
  exists b, find_symbol (add_variables g vl) id = Some b 
         /\ find_var_info (add_variables g vl) b = Some gv
         /\ Mem.range_perm m' b 0 (init_data_list_size gv.(gvar_init)) (perm_globvar gv)
         /\ (gv.(gvar_volatile) = false -> load_store_init_data m' b 0 gv.(gvar_init)).
Proof.
  induction vl; simpl.
  contradiction.
  intros until m'; intro NEXT.
  unfold alloc_variable. destruct a as [id' gv']. simpl.
  caseEq (Mem.alloc m 0 (init_data_list_size (gvar_init gv'))); try congruence.
  intros m1 b ALLOC. 
  caseEq (store_init_data_list m1 b 0 (gvar_init gv')); try congruence.
  intros m2 STORE.
  caseEq (Mem.drop_perm m2 b 0 (init_data_list_size (gvar_init gv')) (perm_globvar gv')); try congruence.
  intros m3 DROP REC NOREPET IN. inv NOREPET.
  exploit Mem.alloc_result; eauto. intro BEQ. 
  destruct IN. inv H.
  exists (Mem.nextblock m); split. 
  rewrite add_variables_same_symb; auto. unfold find_symbol; simpl. 
  rewrite PTree.gss. congruence. 
  split. rewrite add_variables_same_address. unfold find_var_info; simpl.
  rewrite NEXT. apply ZMap.gss.
  simpl. rewrite <- NEXT; omega.
  split. red; intros.
  eapply alloc_variables_perm; eauto.
  eapply Mem.perm_drop_1; eauto. 
  intros NOVOL. 
  apply load_store_init_data_invariant with m2.
  intros. transitivity (Mem.load chunk m3 (Mem.nextblock m) ofs).
  eapply load_alloc_variables; eauto. 
  red. rewrite (Mem.nextblock_drop _ _ _ _ _ _ DROP). 
  rewrite (store_init_data_list_nextblock _ _ _ _ STORE).
  change (Mem.valid_block m1 (Mem.nextblock m)). eauto with mem.
  eapply Mem.load_drop; eauto. repeat right. 
  unfold perm_globvar. rewrite NOVOL. destruct (gvar_readonly gv); auto with mem.
  eapply store_init_data_list_charact; eauto. 

  apply IHvl with m3; auto.
  simpl.
  rewrite (Mem.nextblock_drop _ _ _ _ _ _ DROP). 
  rewrite (store_init_data_list_nextblock _ _ _ _ STORE).
  rewrite (Mem.nextblock_alloc _ _ _ _ _ ALLOC). unfold block in *; omega.
Qed.

End INITMEM.

Definition init_mem (p: program F V) :=
  alloc_variables (globalenv p) Mem.empty p.(prog_vars).

Theorem find_symbol_not_fresh:
  forall p id b m,
  init_mem p = Some m ->
  find_symbol (globalenv p) id = Some b -> Mem.valid_block m b.
Proof.
  unfold init_mem; intros.
  exploit alloc_variables_nextblock; eauto. rewrite Mem.nextblock_empty. intro.
  exploit genv_symb_range; eauto. intros.
  generalize (add_variables_nextvar (prog_vars p) (add_functions empty_genv (prog_funct p))).
  rewrite add_functions_nextvar. simpl genv_nextvar. intro.
  red. rewrite H1. rewrite <- H3. intuition.
Qed.

Theorem find_var_info_not_fresh:
  forall p b gv m,
  init_mem p = Some m ->
  find_var_info (globalenv p) b = Some gv -> Mem.valid_block m b.
Proof.
  unfold init_mem; intros.
  exploit alloc_variables_nextblock; eauto. rewrite Mem.nextblock_empty. intro.
  exploit genv_vars_range; eauto. intros.
  generalize (add_variables_nextvar (prog_vars p) (add_functions empty_genv (prog_funct p))).
  rewrite add_functions_nextvar. simpl genv_nextvar. intro.
  red. rewrite H1. rewrite <- H3. intuition.
Qed.

Theorem find_var_exists:
  forall p id gv m,
  list_norepet (prog_var_names p) ->
  In (id, gv) (prog_vars p) ->
  init_mem p = Some m ->
  exists b, find_symbol (globalenv p) id = Some b
         /\ find_var_info (globalenv p) b = Some gv
         /\ Mem.range_perm m b 0 (init_data_list_size gv.(gvar_init)) (perm_globvar gv)
         /\ (gv.(gvar_volatile) = false -> load_store_init_data (globalenv p) m b 0 gv.(gvar_init)).
Proof.
  intros. exploit alloc_variables_charact; eauto. 
  instantiate (1 := Mem.empty). rewrite add_functions_nextvar. rewrite Mem.nextblock_empty; auto.
  assumption.
Qed.

(** ** Compatibility with memory injections *)

Section INITMEM_INJ.

Variable ge: t.
Variable thr: block.
Hypothesis symb_inject: forall id b, find_symbol ge id = Some b -> b < thr.

Lemma store_init_data_neutral:
  forall m b p id m',
  Mem.inject_neutral thr m ->
  b < thr ->
  store_init_data ge m b p id = Some m' ->
  Mem.inject_neutral thr m'.
Proof.
  intros.
  destruct id; simpl in H1; try (eapply Mem.store_inject_neutral; eauto; fail).
  inv H1; auto.
  revert H1. caseEq (find_symbol ge i); try congruence. intros b' FS ST. 
  eapply Mem.store_inject_neutral; eauto. 
  econstructor. unfold Mem.flat_inj. apply zlt_true; eauto. 
  rewrite Int.add_zero. auto. 
Qed.

Lemma store_init_data_list_neutral:
  forall b idl m p m',
  Mem.inject_neutral thr m ->
  b < thr ->
  store_init_data_list ge m b p idl = Some m' ->
  Mem.inject_neutral thr m'.
Proof.
  induction idl; simpl.
  intros; congruence.
  intros until m'; intros INJ FB.
  caseEq (store_init_data ge m b p a); try congruence. intros. 
  eapply IHidl. eapply store_init_data_neutral; eauto. auto. eauto. 
Qed.

Lemma alloc_variable_neutral:
  forall id m m',
  alloc_variable ge m id = Some m' ->
  Mem.inject_neutral thr m ->
  Mem.nextblock m < thr ->
  Mem.inject_neutral thr m'.
Proof.
  intros until m'. unfold alloc_variable. 
  caseEq (Mem.alloc m 0 (init_data_list_size (gvar_init id#2))); intros m1 b ALLOC.
  caseEq (store_init_data_list ge m1 b 0 (gvar_init id#2)); try congruence.
  intros m2 STORE DROP NEUTRAL NEXT.
  eapply Mem.drop_inject_neutral; eauto. 
  eapply store_init_data_list_neutral with (b := b).
  eapply Mem.alloc_inject_neutral; eauto.
  rewrite (Mem.alloc_result _ _ _ _ _ ALLOC). auto.
  eauto.
  rewrite (Mem.alloc_result _ _ _ _ _ ALLOC). auto.
Qed.

Lemma alloc_variables_neutral:
  forall idl m m',
  alloc_variables ge m idl = Some m' ->
  Mem.inject_neutral thr m ->
  Mem.nextblock m' <= thr ->
  Mem.inject_neutral thr m'.
Proof.
  induction idl; simpl.
  intros. congruence.
  intros until m'. caseEq (alloc_variable ge m a); try congruence. intros.
  assert (Mem.nextblock m' = Mem.nextblock m + Z_of_nat(length (a :: idl))).
  eapply alloc_variables_nextblock with ge. simpl. rewrite H. auto. 
  simpl length in H3. rewrite inj_S in H3. 
  exploit alloc_variable_neutral; eauto. unfold block in *; omega.
Qed.

End INITMEM_INJ.

Theorem initmem_inject:
  forall p m,
  init_mem p = Some m ->
  Mem.inject (Mem.flat_inj (Mem.nextblock m)) m m.
Proof.
  unfold init_mem; intros.
  apply Mem.neutral_inject. 
  eapply alloc_variables_neutral; eauto. 
  intros. exploit find_symbol_not_fresh; eauto.
  apply Mem.empty_inject_neutral.
  omega.
Qed.

End GENV.

(** * Commutation with program transformations *)

(** ** Commutation with matching between programs. *)

Section MATCH_PROGRAMS.

Variables A B V W: Type.
Variable match_fun: A -> B -> Prop.
Variable match_varinfo: V -> W -> Prop.

Inductive match_globvar: globvar V -> globvar W -> Prop :=
  | match_globvar_intro: forall info1 info2 init ro vo,
      match_varinfo info1 info2 ->
      match_globvar (mkglobvar info1 init ro vo) (mkglobvar info2 init ro vo).

Record match_genvs (ge1: t A V) (ge2: t B W): Prop := {
  mge_nextfun: genv_nextfun ge1 = genv_nextfun ge2;
  mge_nextvar: genv_nextvar ge1 = genv_nextvar ge2;
  mge_symb:    genv_symb ge1 = genv_symb ge2;
  mge_funs:
    forall b f, ZMap.get b (genv_funs ge1) = Some f ->
    exists tf, ZMap.get b (genv_funs ge2) = Some tf /\ match_fun f tf;
  mge_rev_funs:
    forall b tf, ZMap.get b (genv_funs ge2) = Some tf ->
    exists f, ZMap.get b (genv_funs ge1) = Some f /\ match_fun f tf;
  mge_vars:
    forall b v, ZMap.get b (genv_vars ge1) = Some v ->
    exists tv, ZMap.get b (genv_vars ge2) = Some tv /\ match_globvar v tv;
  mge_rev_vars:
    forall b tv, ZMap.get b (genv_vars ge2) = Some tv ->
    exists v, ZMap.get b (genv_vars ge1) = Some v /\ match_globvar v tv
}.

Lemma add_function_match:
  forall ge1 ge2 id f1 f2,
  match_genvs ge1 ge2 ->
  match_fun f1 f2 ->
  match_genvs (add_function ge1 (id, f1)) (add_function ge2 (id, f2)).
Proof.
  intros. destruct H. constructor; simpl. 
  congruence. congruence. congruence.
  rewrite mge_nextfun0. intros. rewrite ZMap.gsspec in H. rewrite ZMap.gsspec. 
  destruct (ZIndexed.eq b (genv_nextfun ge2)). 
  exists f2; split; congruence.
  eauto.
  rewrite mge_nextfun0. intros. rewrite ZMap.gsspec in H. rewrite ZMap.gsspec. 
  destruct (ZIndexed.eq b (genv_nextfun ge2)). 
  exists f1; split; congruence.
  eauto.
  auto.
  auto.
Qed.

Lemma add_functions_match:
  forall fl1 fl2, list_forall2 (match_funct_entry match_fun) fl1 fl2 ->
  forall ge1 ge2, match_genvs ge1 ge2 ->
  match_genvs (add_functions ge1 fl1) (add_functions ge2 fl2).
Proof.
  induction 1; intros; simpl. 
  auto.
  destruct a1 as [id1 f1]; destruct b1 as [id2 f2].
  destruct H. subst. apply IHlist_forall2. apply add_function_match; auto.
Qed.

Lemma add_variable_match:
  forall ge1 ge2 id v1 v2,
  match_genvs ge1 ge2 ->
  match_globvar v1 v2 ->
  match_genvs (add_variable ge1 (id, v1)) (add_variable ge2 (id, v2)).
Proof.
  intros. destruct H. constructor; simpl. 
  congruence. congruence. congruence.
  auto.
  auto.
  rewrite mge_nextvar0. intros. rewrite ZMap.gsspec in H. rewrite ZMap.gsspec. 
  destruct (ZIndexed.eq b (genv_nextvar ge2)). 
  exists v2; split; congruence.
  eauto.
  rewrite mge_nextvar0. intros. rewrite ZMap.gsspec in H. rewrite ZMap.gsspec. 
  destruct (ZIndexed.eq b (genv_nextvar ge2)). 
  exists v1; split; congruence.
  eauto.
Qed.

Lemma add_variables_match:
  forall vl1 vl2, list_forall2 (match_var_entry match_varinfo) vl1 vl2 ->
  forall ge1 ge2, match_genvs ge1 ge2 ->
  match_genvs (add_variables ge1 vl1) (add_variables ge2 vl2).
Proof.
  induction 1; intros; simpl. 
  auto.
  inv H. apply IHlist_forall2. apply add_variable_match; auto. constructor; auto.
Qed.

Variable p: program A V.
Variable p': program B W.
Hypothesis progmatch: match_program match_fun match_varinfo p p'.

Lemma globalenvs_match:
  match_genvs (globalenv p) (globalenv p').
Proof.
  unfold globalenv. destruct progmatch. destruct H0. 
  apply add_variables_match; auto. apply add_functions_match; auto. 
  constructor; simpl; auto; intros; rewrite ZMap.gi in H2; congruence.
Qed.

Theorem find_funct_ptr_match:
  forall (b : block) (f : A),
  find_funct_ptr (globalenv p) b = Some f ->
  exists tf : B,
  find_funct_ptr (globalenv p') b = Some tf /\ match_fun f tf.
Proof (mge_funs globalenvs_match).

Theorem find_funct_ptr_rev_match:
  forall (b : block) (tf : B),
  find_funct_ptr (globalenv p') b = Some tf ->
  exists f : A,
  find_funct_ptr (globalenv p) b = Some f /\ match_fun f tf.
Proof (mge_rev_funs globalenvs_match).

Theorem find_funct_match:
  forall (v : val) (f : A),
  find_funct (globalenv p) v = Some f ->
  exists tf : B, find_funct (globalenv p') v = Some tf /\ match_fun f tf.
Proof.
  intros. exploit find_funct_inv; eauto. intros [b EQ]. subst v. 
  rewrite find_funct_find_funct_ptr in H. 
  rewrite find_funct_find_funct_ptr.
  apply find_funct_ptr_match. auto.
Qed.

Theorem find_funct_rev_match:
  forall (v : val) (tf : B),
  find_funct (globalenv p') v = Some tf ->
  exists f : A, find_funct (globalenv p) v = Some f /\ match_fun f tf.
Proof.
  intros. exploit find_funct_inv; eauto. intros [b EQ]. subst v. 
  rewrite find_funct_find_funct_ptr in H. 
  rewrite find_funct_find_funct_ptr.
  apply find_funct_ptr_rev_match. auto.
Qed.

Theorem find_var_info_match:
  forall (b : block) (v : globvar V),
  find_var_info (globalenv p) b = Some v ->
  exists tv,
  find_var_info (globalenv p') b = Some tv /\ match_globvar v tv.
Proof (mge_vars globalenvs_match).

Theorem find_var_info_rev_match:
  forall (b : block) (tv : globvar W),
  find_var_info (globalenv p') b = Some tv ->
  exists v,
  find_var_info (globalenv p) b = Some v /\ match_globvar v tv.
Proof (mge_rev_vars globalenvs_match).

Theorem find_symbol_match:
  forall (s : ident),
  find_symbol (globalenv p') s = find_symbol (globalenv p) s.
Proof.
  intros. destruct globalenvs_match. unfold find_symbol. congruence. 
Qed.

Lemma store_init_data_list_match:
  forall idl m b ofs,
  store_init_data_list (globalenv p') m b ofs idl =
  store_init_data_list (globalenv p) m b ofs idl.
Proof.
  induction idl; simpl; intros. 
  auto.
  assert (store_init_data (globalenv p') m b ofs a =
          store_init_data (globalenv p) m b ofs a).
  destruct a; simpl; auto. rewrite find_symbol_match. auto. 
  rewrite H. destruct (store_init_data (globalenv p) m b ofs a); auto. 
Qed.

Lemma alloc_variables_match:
  forall vl1 vl2, list_forall2 (match_var_entry match_varinfo) vl1 vl2 ->
  forall m,
  alloc_variables (globalenv p') m vl2 = alloc_variables (globalenv p) m vl1.
Proof.
  induction 1; intros; simpl.
  auto.
  inv H. 
  unfold alloc_variable; simpl. 
  destruct (Mem.alloc m 0 (init_data_list_size init)). 
  rewrite store_init_data_list_match. 
  destruct (store_init_data_list (globalenv p) m0 b 0 init); auto.
  change (perm_globvar (mkglobvar info2 init ro vo))
    with (perm_globvar (mkglobvar info1 init ro vo)).
  destruct (Mem.drop_perm m1 b 0 (init_data_list_size init)
    (perm_globvar (mkglobvar info1 init ro vo))); auto.
Qed.

Theorem init_mem_match:
  forall m, init_mem p = Some m -> init_mem p' = Some m.
Proof.
  intros. rewrite <- H. unfold init_mem. destruct progmatch. destruct H1. 
  apply alloc_variables_match; auto. 
Qed.

End MATCH_PROGRAMS.

Section TRANSF_PROGRAM_PARTIAL2.

Variable A B V W: Type.
Variable transf_fun: A -> res B.
Variable transf_var: V -> res W.
Variable p: program A V.
Variable p': program B W.
Hypothesis transf_OK:
  transform_partial_program2 transf_fun transf_var p = OK p'.

Remark prog_match:
  match_program
    (fun fd tfd => transf_fun fd = OK tfd)
    (fun info tinfo => transf_var info = OK tinfo)
    p p'.
Proof.
  apply transform_partial_program2_match; auto.
Qed.

Theorem find_funct_ptr_transf_partial2:
  forall (b: block) (f: A),
  find_funct_ptr (globalenv p) b = Some f ->
  exists f',
  find_funct_ptr (globalenv p') b = Some f' /\ transf_fun f = OK f'.
Proof.
  intros. 
  exploit find_funct_ptr_match. eexact prog_match. eauto. 
  intros [tf [X Y]]. exists tf; auto.
Qed.

Theorem find_funct_ptr_rev_transf_partial2:
  forall (b: block) (tf: B),
  find_funct_ptr (globalenv p') b = Some tf ->
  exists f, find_funct_ptr (globalenv p) b = Some f /\ transf_fun f = OK tf.
Proof.
  intros. 
  exploit find_funct_ptr_rev_match. eexact prog_match. eauto. auto. 
Qed.

Theorem find_funct_transf_partial2:
  forall (v: val) (f: A),
  find_funct (globalenv p) v = Some f ->
  exists f',
  find_funct (globalenv p') v = Some f' /\ transf_fun f = OK f'.
Proof.
  intros. 
  exploit find_funct_match. eexact prog_match. eauto. 
  intros [tf [X Y]]. exists tf; auto.
Qed.

Theorem find_funct_rev_transf_partial2:
  forall (v: val) (tf: B),
  find_funct (globalenv p') v = Some tf ->
  exists f, find_funct (globalenv p) v = Some f /\ transf_fun f = OK tf.
Proof.
  intros. 
  exploit find_funct_rev_match. eexact prog_match. eauto. auto. 
Qed.

Theorem find_var_info_transf_partial2:
  forall (b: block) (v: globvar V),
  find_var_info (globalenv p) b = Some v ->
  exists v',
  find_var_info (globalenv p') b = Some v' /\ transf_globvar transf_var v = OK v'.
Proof.
  intros. 
  exploit find_var_info_match. eexact prog_match. eauto. 
  intros [tv [X Y]]. exists tv; split; auto. inv Y. unfold transf_globvar; simpl.
  rewrite H0; simpl. auto.
Qed.

Theorem find_var_info_rev_transf_partial2:
  forall (b: block) (v': globvar W),
  find_var_info (globalenv p') b = Some v' ->
  exists v,
  find_var_info (globalenv p) b = Some v /\ transf_globvar transf_var v = OK v'.
Proof.
  intros. 
  exploit find_var_info_rev_match. eexact prog_match. eauto. 
  intros [v [X Y]]. exists v; split; auto. inv Y. unfold transf_globvar; simpl.
  rewrite H0; simpl. auto.
Qed.

Theorem find_symbol_transf_partial2:
  forall (s: ident),
  find_symbol (globalenv p') s = find_symbol (globalenv p) s.
Proof.
  intros. eapply find_symbol_match. eexact prog_match.
Qed.

Theorem init_mem_transf_partial2:
  forall m, init_mem p = Some m -> init_mem p' = Some m.
Proof.
  intros. eapply init_mem_match. eexact prog_match. auto.
Qed.

End TRANSF_PROGRAM_PARTIAL2.

Section TRANSF_PROGRAM_PARTIAL.

Variable A B V: Type.
Variable transf: A -> res B.
Variable p: program A V.
Variable p': program B V.
Hypothesis transf_OK: transform_partial_program transf p = OK p'.

Remark transf2_OK:
  transform_partial_program2 transf (fun x => OK x) p = OK p'.
Proof.
  rewrite <- transf_OK. 
  unfold transform_partial_program2, transform_partial_program.
  destruct (map_partial prefix_name transf (prog_funct p)); auto.
  simpl. replace (transf_globvar (fun (x : V) => OK x)) with (fun (v: globvar V) => OK v).
  rewrite map_partial_identity; auto.
  apply extensionality; intros. destruct x; auto.
Qed.

Theorem find_funct_ptr_transf_partial:
  forall (b: block) (f: A),
  find_funct_ptr (globalenv p) b = Some f ->
  exists f',
  find_funct_ptr (globalenv p') b = Some f' /\ transf f = OK f'.
Proof.
  exact (@find_funct_ptr_transf_partial2 _ _ _ _ _ _ _ _ transf2_OK).
Qed.

Theorem find_funct_ptr_rev_transf_partial:
  forall (b: block) (tf: B),
  find_funct_ptr (globalenv p') b = Some tf ->
  exists f, find_funct_ptr (globalenv p) b = Some f /\ transf f = OK tf.
Proof.
  exact (@find_funct_ptr_rev_transf_partial2 _ _ _ _ _ _ _ _ transf2_OK).
Qed.

Theorem find_funct_transf_partial:
  forall (v: val) (f: A),
  find_funct (globalenv p) v = Some f ->
  exists f',
  find_funct (globalenv p') v = Some f' /\ transf f = OK f'.
Proof.
  exact (@find_funct_transf_partial2 _ _ _ _ _ _ _ _ transf2_OK).
Qed.

Theorem find_funct_rev_transf_partial:
  forall (v: val) (tf: B),
  find_funct (globalenv p') v = Some tf ->
  exists f, find_funct (globalenv p) v = Some f /\ transf f = OK tf.
Proof.
  exact (@find_funct_rev_transf_partial2 _ _ _ _ _ _ _ _ transf2_OK).
Qed.

Theorem find_symbol_transf_partial:
  forall (s: ident),
  find_symbol (globalenv p') s = find_symbol (globalenv p) s.
Proof.
  exact (@find_symbol_transf_partial2 _ _ _ _ _ _ _ _ transf2_OK).
Qed.

Theorem find_var_info_transf_partial:
  forall (b: block),
  find_var_info (globalenv p') b = find_var_info (globalenv p) b.
Proof.
  intros. case_eq (find_var_info (globalenv p) b); intros.
  exploit find_var_info_transf_partial2. eexact transf2_OK. eauto. 
  intros [v' [P Q]]. monadInv Q. rewrite P. inv EQ. destruct g; auto. 
  case_eq (find_var_info (globalenv p') b); intros.
  exploit find_var_info_rev_transf_partial2. eexact transf2_OK. eauto.
  intros [v' [P Q]]. monadInv Q. inv EQ. congruence. 
  auto.
Qed.

Theorem init_mem_transf_partial:
  forall m, init_mem p = Some m -> init_mem p' = Some m.
Proof.
  exact (@init_mem_transf_partial2 _ _ _ _ _ _ _ _ transf2_OK).
Qed.

End TRANSF_PROGRAM_PARTIAL.

Section TRANSF_PROGRAM.

Variable A B V: Type.
Variable transf: A -> B.
Variable p: program A V.
Let tp := transform_program transf p.

Remark transf_OK:
  transform_partial_program (fun x => OK (transf x)) p = OK tp.
Proof.
  unfold tp, transform_program, transform_partial_program.
  rewrite map_partial_total. reflexivity.
Qed.

Theorem find_funct_ptr_transf:
  forall (b: block) (f: A),
  find_funct_ptr (globalenv p) b = Some f ->
  find_funct_ptr (globalenv tp) b = Some (transf f).
Proof.
  intros. 
  destruct (@find_funct_ptr_transf_partial _ _ _ _ _ _ transf_OK _ _ H)
  as [f' [X Y]]. congruence.
Qed.

Theorem find_funct_ptr_rev_transf:
  forall (b: block) (tf: B),
  find_funct_ptr (globalenv tp) b = Some tf ->
  exists f, find_funct_ptr (globalenv p) b = Some f /\ transf f = tf.
Proof.
  intros. exploit find_funct_ptr_rev_transf_partial. eexact transf_OK. eauto.
  intros [f [X Y]]. exists f; split. auto. congruence.
Qed.

Theorem find_funct_transf:
  forall (v: val) (f: A),
  find_funct (globalenv p) v = Some f ->
  find_funct (globalenv tp) v = Some (transf f).
Proof.
  intros. 
  destruct (@find_funct_transf_partial _ _ _ _ _ _ transf_OK _ _ H)
  as [f' [X Y]]. congruence.
Qed.

Theorem find_funct_rev_transf:
  forall (v: val) (tf: B),
  find_funct (globalenv tp) v = Some tf ->
  exists f, find_funct (globalenv p) v = Some f /\ transf f = tf.
Proof.
  intros. exploit find_funct_rev_transf_partial. eexact transf_OK. eauto.
  intros [f [X Y]]. exists f; split. auto. congruence.
Qed.

Theorem find_symbol_transf:
  forall (s: ident),
  find_symbol (globalenv tp) s = find_symbol (globalenv p) s.
Proof.
  exact (@find_symbol_transf_partial _ _ _ _ _ _ transf_OK).
Qed.

Theorem find_var_info_transf:
  forall (b: block),
  find_var_info (globalenv tp) b = find_var_info (globalenv p) b.
Proof.
  exact (@find_var_info_transf_partial _ _ _ _ _ _ transf_OK).
Qed.

Theorem init_mem_transf:
  forall m, init_mem p = Some m -> init_mem tp = Some m.
Proof.
  exact (@init_mem_transf_partial _ _ _ _ _ _ transf_OK).
Qed.

End TRANSF_PROGRAM.

End Genv.

(*Require Import Globalenvs Memory.*)
Require Import Csyntax Csem. 
Require Import Arm6_State Arm6_Proc Arm6_SCC adc_compcert2 Bitvec.


Definition env0 := (PTree.empty (block * type)).

Definition mem1 := Genv.init_mem program_fundef_type. 

Definition blk1 := 
match mem1 with
|Some m => let (m',b):= Mem.alloc m 0 1 in Some b
|None => None
end.

Definition env1 := 
match blk1 with
|Some b => 
  PTree.set N_flag (b,Tint I8 Unsigned) env0
|None => env0
end.

Definition store_value_of_type' (ty_dest: type) (m: Mem.mem) (loc: block) (ofs: int) (v: val) : option Mem.mem :=
  match access_mode ty_dest with
  | By_value chunk => Mem.storev chunk m (Vptr loc ofs) v
  | By_reference => None
  | By_nothing => None
  end.

Definition load_value_of_type' (ty: type) (m: Mem.mem) (b: block) (ofs: int) : option val :=
  match access_mode ty with
  | By_value chunk => Mem.loadv chunk m (Vptr b ofs)
  | By_reference => Some (Vptr b ofs)
  | By_nothing => None
  end.

Definition cpsr_map (coqcpsr: word) :option Mem.mem:=
  let nflag := coqcpsr[31] in
  let zflag := coqcpsr[30] in
  let cflag := coqcpsr[29] in
  let vflag := coqcpsr[28] in
  let qflag := coqcpsr[27] in
  let jflag := coqcpsr[24] in
  let ge0 := coqcpsr[16] in
  let ge1 := coqcpsr[17] in
  let ge2 := coqcpsr[18] in
  let ge3 := coqcpsr[19] in
  let eflag := coqcpsr[9] in
  let aflag := coqcpsr[8] in
  let iflag := coqcpsr[7] in
  let fflag := coqcpsr[6] in
  let tflag := coqcpsr[5] in
  let bg := add coqcpsr[23 # 20] coqcpsr[15 # 10] in
    match mem1 with
      |Some m => 
        (match (PTree.get N_flag env1) with
           |Some (b,t) => store_value_of_type' T3 m b Int.zero (Vint nflag)
           |None => None
         end)
      |None => None 
    end.

Definition ccpsr_val :=
  match cpsr_map (repr 0) with
    |Some m => 
      (match (PTree.get N_flag env0) with
         |Some (b,t) => load_value_of_type' t m b Int.zero
         |None => None
       end)
    |None => None
  end.

Definition nflag_blk :=
  match (PTree.get N_flag env1) with
    |Some (b,t) => Some b
    |None => None
  end.

Set Printing Depth 10.
Transparent Mem.alloc.
About Mem.alloc.
Transparent Mem.range_perm_dec.
About Mem.range_perm_dec.
Transparent Mem.store.
Opaque Mem.valid_access_dec.
Eval lazy in ccpsr_val.

Theorem tt : {true = true}+{True}.
right; exact I.
Qed.

About tt.
Opaque tt.
About tt.
Transparent tt.
About tt.

Transparent Mem.range_perm_dec.
About Mem.range_perm_dec.

Check ccpsr_val.
Print val.