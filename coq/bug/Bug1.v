(* efficiency problem related to termination checker in 8.2,
solved in 8.3 *)

Require Import Bool.

(* 
La plus grande partie de ce qui suit revient a genere de gros calculs
tout d'abord sur le type Z, puis sur le type word
*)

(* BEGIN calculasse Z, pris essentiellement chez Xavier *)

Definition Nbit := 31%nat.
Definition Zbit := 30%nat.
Definition Cbit := 29%nat.
Definition Vbit := 28%nat.

Require Import ZArith.
Open Scope Z_scope.


Definition wordsize : nat := 32%nat.
Definition modulus : Z := two_power_nat wordsize.
Record int: Type := mkint { intval: Z; intrange: 0 <= intval < modulus }.

Lemma two_power_nat_O : two_power_nat O = 1.
Proof. reflexivity. Qed.

Lemma two_power_nat_pos : forall n : nat, two_power_nat n > 0.
Proof.
  induction n. rewrite two_power_nat_O. omega.
  rewrite two_power_nat_S. omega.
Qed.

Lemma mod_in_range:
  forall x, 0 <= Zmod x modulus < modulus.
Proof.
  intro.
  exact (Z_mod_lt x modulus (two_power_nat_pos wordsize)).
Qed.
Definition repr (x: Z) : int := 
  mkint (Zmod x modulus) (mod_in_range x).

Definition unsigned (n: int) : Z := intval n.
Definition Z_bin_decomp (x: Z) : bool * Z :=
  match x with
  | Z0 => (false, 0)
  | Zpos p =>
      match p with
      | xI q => (true, Zpos q)
      | xO q => (false, Zpos q)
      | xH => (true, 0)
      end
  | Zneg p =>
      match p with
      | xI q => (true, Zneg q - 1)
      | xO q => (false, Zneg q)
      | xH => (true, -1)
      end
  end.
Definition zeq: forall (x y: Z), {x = y} + {x <> y} := Z_eq_dec.

Fixpoint bits_of_Z (n: nat) (x: Z) {struct n}: Z -> bool :=
  match n with
  | O =>
      (fun i: Z => false)
  | S m =>
      let (b, y) := Z_bin_decomp x in
      let f := bits_of_Z m y in
      (fun i: Z => if zeq i 0 then b else f (i - 1))
  end.

Definition Z_shift_add (b: bool) (x: Z) :=
  if b then 2 * x + 1 else 2 * x.

Fixpoint Z_of_bits (n: nat) (f: Z -> bool) {struct n}: Z :=
  match n with
  | O => 0
  | S m => Z_shift_add (f 0) (Z_of_bits m (fun i => f (i + 1)))
  end.


Definition bitwise_binop (f: bool -> bool -> bool) (x y: int) :=
  let fx := bits_of_Z wordsize (unsigned x) in
  let fy := bits_of_Z wordsize (unsigned y) in
  repr (Z_of_bits wordsize (fun i => f (fx i) (fy i))).

Definition and (x y: int): int := bitwise_binop andb x y.

(* END calculasse Z *)


(* BEGIN calculasse word *)

Notation word := int.
Coercion intval : word >-> Z.

Fixpoint masks_aux (n k : nat) : Z :=
  match k with
    | O => two_power_nat n
    | S k' => two_power_nat n + masks_aux (S n) k'
  end.
Definition masks (n p : nat) : word := repr (masks_aux n (p-n)).

Definition bits (k l : nat) (w : word) : word := and (masks k l) w.
Definition bits_val (k l : nat) (w : word) : Z :=
  bits k l w / two_power_nat k.

Definition mask (n : nat) : word := repr (two_power_nat n).
Definition bit (k : nat) (w : word) : word := and (mask k) w.
Definition zne (x y : Z) : bool := if Z_eq_dec x y then false else true.
Definition is_set (k : nat) (w : word) : bool := zne (bit k w) 0.

(* *)

Definition FConditionPassed (w : word) : bool :=
  match bits_val 28 31 w with
    | (*0000*) 0 => (* Z set *) is_set Zbit w
    | (*0001*) 1 => (* Z clear *) negb (is_set Zbit w)
    | (*0010*) 2 => (* C set *) is_set Cbit w
    | (*0011*) 3 => (* C clear *) negb (is_set Cbit w)
    | (*0100*) 4 => (* N set *) is_set Cbit w
    | (*0101*) 5 => (* N clear *) negb (is_set Cbit w)
    | (*0110*) 6 => (* V set *) is_set Vbit w
    | (*0111*) 7 => (* V clear *) negb (is_set Vbit w)
    | (*1000*) 8 => (* C set and Z clear *)
      andb (is_set Cbit w) (negb (is_set Zbit w))
    | (*1001*) 9 => (* C clear or Z set *)
      orb (negb (is_set Cbit w)) (is_set Zbit w)
    | (*1010*) 10 => (* N set and V set, or N clear and V clear (N==V) *)
      eqb (is_set Nbit w) (is_set Vbit w)
    | (*1011*) 11 => (* N set and V clear, or N clear and V set (N!=V) *)
      negb (eqb (is_set Nbit w) (is_set Vbit w))
    | (*1100*) 12 => (* Z clear, and either N set and V set,
         or N clear and V clear (Z==0,N==V) *)
      andb (negb (is_set Zbit w)) (eqb (is_set Nbit w) (is_set Vbit w))
    | (*1101*) 13 => (* Z set, or N set and V clear, or N clear and V set
         (Z==1 or N!=V) *)
      orb (is_set Zbit w) (negb (eqb (is_set Nbit w) (is_set Vbit w)))
    | _ => true
  end.

(* END calculasse word *)


(* 
Point fixe dont le type checking pedale dans le yaourt. 
Si on enleve des cas dans [FConditionPassed] ci-dessus,
ca pedale d'autant moins.
On ne voit pas pourquoi [FConditionPassed w] est examine
dans la def de pt fixe.
*)
Inductive inst : Type :=
| Unpredictable
| IfThen (i : inst)
.

Fixpoint interp (w : word) (i : inst) : option bool :=
  match i with
    | Unpredictable => None
    | IfThen i =>
      if FConditionPassed w then interp w i else None
  end.

