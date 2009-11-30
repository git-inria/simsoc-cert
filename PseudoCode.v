(**
SimSoC-Cert, a Coq library on processor architectures for embedded systems.
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

Inductive exp : Type :=
| Var (k : nat)
| Word (w : word)
| Flag (n : nat)
| Reg (e : exp)
| Bit (n : nat) (e : exp)
| If (be : bexp) (e1 e2 : exp)
| Add (e1 e2 : exp)
| CarryFrom_add2 (e1 e2 : exp)
| OverflowFrom_add2 (e1 e2 : exp)
| CarryFrom_add3 (e1 e2 e3 : exp)
| OverflowFrom_add3 (e1 e2 e3 : exp)

with bexp : Type :=
| Eq (e1 e2 : exp)
| ConditionPassed
| BAnd (be1 be2 : bexp).

(****************************************************************************)
(** Pseudo-code expressions used as left hand-side of affectations *)
(****************************************************************************)

Inductive lexp : Type :=
| LCPSR
| LReg (e : exp)
| LFlag (n : nat).

(****************************************************************************)
(** Pseudo-code instructions *)
(****************************************************************************)

Inductive inst : Type :=
| Unpredictable
| Seq (i1 i2 : inst)
| Affect (le : lexp) (e : exp)
| IfThen (be : bexp) (i : inst)
| IfThenElse (be : bexp) (i1 i2 : inst)
| Affect_CPSR_SPSR.

(****************************************************************************)
(** Semantics of pseudo-code expressions *)
(****************************************************************************)

Section interp.

Variable word_of_var : nat -> word.
Variable m : processor_mode.

Section exp.

Variable s : state.

Fixpoint word_of_exp (e : exp) : word :=
  match e with
    | Var k => word_of_var k
    | Word w => w
    | Flag n => bit n (cpsr s)
    | Reg e => reg_content s m (mk_reg_num (word_of_exp e))
    | Bit n e => bit n (word_of_exp e)
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

with bool_of_bexp (be : bexp) : bool :=
  match be with
    | Eq e1 e2 => zeq (word_of_exp e1) (word_of_exp e2)
    | ConditionPassed => Functions.ConditionPassed (cpsr s)
    | BAnd be1 be2 => andb (bool_of_bexp be1) (bool_of_bexp be2)
  end.

End exp.

(****************************************************************************)
(** Semantics of pseudo-code instructions *)
(****************************************************************************)

Definition update (le : lexp) (w : word) (s : state) : bool * state :=
  match le with
    | LCPSR => (true, update_cpsr w s)
    | LReg e => let k := word_of_exp s e in
      (zne k 15, update_reg m (mk_reg_num k) w s)
    | LFlag n => (true, update_cpsr (update n w (cpsr s)) s)
  end.

(* state in which all expressions are evaluated *)
Variable s0 : state.

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
    | Affect le e => Some (update le (word_of_exp s0 e) s)
    | IfThen be i =>
      if bool_of_bexp s0 be then interp_aux s i else Some (true, s)
    | IfThenElse be i1 i2 =>
      if bool_of_bexp s0 be then interp_aux s i1 else interp_aux s i2
    | Affect_CPSR_SPSR =>
      match m with
        | exn e => Some (true, update_cpsr (spsr s0 e) s)
        | _ => None
      end
  end.

Definition interp := interp_aux s0.

End interp.
