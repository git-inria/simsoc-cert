(**
SimSoC-Cert, a toolkit for generating certified processor simulators.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Pseudocode syntax and semantics.
*)

Require Import Bitvec.
Require Import State.
Require Import ZArith.
Require Import Functions.
Require Import Integers. Import Int.
Require Import Coqlib.
Require Import Util.

Open Scope Z_scope.

(****************************************************************************)
(* Pseudo-code expressions *)
(****************************************************************************)

Inductive range : Type := All | Bit (n : nat) | Bits (p n : nat).

Inductive exp : Type :=
| Var (k : nat)
| Word (w : word)
| State (se : sexp) (r : range)
| If (be : bexp) (e1 e2 : exp)
| Add (e1 e2 : exp)
| CarryFrom_add2 (e1 e2 : exp)
| OverflowFrom_add2 (e1 e2 : exp)
| CarryFrom_add3 (e1 e2 e3 : exp)
| OverflowFrom_add3 (e1 e2 e3 : exp)

with sexp : Type :=
| CPSR
| SPSR (em : processor_exception_mode)
| Reg (e : exp)
| Reg_exn (em : processor_exception_mode) (e : exp)

with bexp : Type :=
| Eq (e1 e2 : exp)
| ConditionPassed
| BAnd (be1 be2 : bexp).

Coercion Word : word >-> exp.

Definition W (p : positive) : exp := Word (repr (Zpos p)).

(****************************************************************************)
(** Pseudo-code instructions *)
(****************************************************************************)

Inductive inst : Type :=
| Unpredictable
| Seq (i1 i2 : inst)
| Affect (se : sexp) (r : range) (e : exp)
| IfThen (be : bexp) (i : inst)
| IfThenElse (be : bexp) (i1 i2 : inst)
| Affect_CPSR_SPSR.

(****************************************************************************)
(** Semantics of pseudo-code expressions *)
(****************************************************************************)

Definition word_of_range (r : range) (w : word) : word :=
  match r with
    | All => w
    | Bit n => w[n]
    | Bits p n => w[p#n]
  end.

Section interp.

Variable word_of_var : nat -> word.

Definition empty (_ : nat) : word := w0.
Definition assoc := @update_map _ eq_nat_dec word.

(* state in which expressions are evaluated *)
Variable s0 : state.
Variable m : processor_mode.

Fixpoint word_of_exp (e : exp) : word :=
  match e with
    | Var k => word_of_var k
    | Word w => w
    | State se r => word_of_range r (word_of_sexp se)
    | If be e1 e2 =>
      if bool_of_bexp be then word_of_exp e1 else word_of_exp e2
    | Add e1 e2 => add (word_of_exp e1) (word_of_exp e2)
    | CarryFrom_add2 e1 e2 =>
      Functions.CarryFrom_add2 (word_of_exp e1) (word_of_exp e2)
    | OverflowFrom_add2 e1 e2 =>
      Functions.OverflowFrom_add2 (word_of_exp e1) (word_of_exp e2)
    | CarryFrom_add3 e1 e2 e3 => Functions.CarryFrom_add3
      (word_of_exp e1) (word_of_exp e2) (word_of_exp e3)
    | OverflowFrom_add3 e1 e2 e3 => Functions.OverflowFrom_add3
      (word_of_exp e1) (word_of_exp e2) (word_of_exp e3)
  end

with word_of_sexp (se : sexp) : word :=
  match se with
    | CPSR => cpsr s0
    | SPSR em => spsr s0 em
    | Reg e => reg_content s0 m (mk_reg_num (word_of_exp e))
    | Reg_exn em e => (*FIXME*) cpsr s0
  end

with bool_of_bexp (be : bexp) : bool :=
  match be with
    | Eq e1 e2 => zeq (word_of_exp e1) (word_of_exp e2)
    | ConditionPassed => true (*FIXME:Functions.ConditionPassed (cpsr s0)*)
    | BAnd be1 be2 => andb (bool_of_bexp be1) (bool_of_bexp be2)
  end.

(****************************************************************************)
(** Semantics of pseudo-code instructions *)
(****************************************************************************)

Definition update_range (r : range) (v w : word) : word :=
  match r with
    | All => v
    | Bit n => update_bit n v w
    | Bits p n => update_bits p n v w
  end.

Definition update (se : sexp) (r : range) (v : word) (s : state)
  : bool * state :=
  match se with
    | CPSR => (true, update_cpsr (update_range r v (cpsr s)) s)
    | SPSR em => (true, update_spsr em (update_range r v (spsr s em)) s)
    | Reg e => let k := mk_reg_num (word_of_exp e) in
      (zne k 15, update_reg m k (update_range r v (reg_content s m k)) s)
    | Reg_exn em e => (*FIXME*) (true, s)
  end.

Fixpoint interp_aux (s : state) (i : inst) : result :=
  match i with
    | Unpredictable => None
    | Seq i1 i2 =>
      match interp_aux s i1 with
        | None => None
        | Some (b1, s1) =>
          match interp_aux s1 i2 with
            | None => None
            | Some (b2, s2) => Some (andb b1 b2, s2)
          end
      end
    | Affect le r e => Some (update le r (word_of_exp e) s)
    | IfThen be i =>
      if bool_of_bexp be then interp_aux s i else Some (true, s)
    | IfThenElse be i1 i2 =>
      if bool_of_bexp be then interp_aux s i1 else interp_aux s i2
    | Affect_CPSR_SPSR =>
      match m with
        | exn e => Some (true, update_cpsr (spsr s0 e) s)
        | _ => None
      end
  end.

Definition interp := interp_aux s0.

End interp.
