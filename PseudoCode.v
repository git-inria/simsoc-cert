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

(****************************************************************************)
(** Types of pseudo-code values *)
(****************************************************************************)

Inductive sort : Type := SBool | SRegNum | SWord.

Definition type_of_sort (s : sort) : Type :=
  match s with
    | SBool => bool
    | SRegNum => reg_num
    | SWord => word
  end.

Record sorted_val : Type := mk_sorted_val {
  sv_sort : sort;
  sv_val :> type_of_sort sv_sort }.

(****************************************************************************)
(* Pseudo-code expressions *)
(****************************************************************************)

Inductive exp : Type :=
| Var (k : nat)
| Reg (k : reg_num)
| Word (w : word)
| Flag (n : nat)
| Bit (n : nat) (k : reg_num)
| If (b : bexp) (e1 e2 : exp)
| Add (e1 e2 : exp)
| CarryFrom_add2 (e1 e2 : exp)
| OverflowFrom_add2 (e1 e2 : exp)
| CarryFrom_add3 (e1 e2 e3 : exp)
| OverflowFrom_add3 (e1 e2 e3 : exp)

with bexp : Type :=
| Eq (e1 e2 : exp)
| CurrentModeHasSPSR.

(****************************************************************************)
(** Pseudo-code expressions used as left hand-side of affectations *)
(****************************************************************************)

Inductive lexp : Type :=
| LCPSR
| LReg (k : reg_num)
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

Variable sorted_val_of_var : nat -> sorted_val.
Variable m : processor_mode.

Definition word_of_sort (s : state) (t : sort) : type_of_sort t -> word :=
  match t as t return type_of_sort t -> word with
    | SBool => word_of_bool
    | SRegNum => reg_content s m
    | SWord => fun v => v
  end.

Definition word_of_var (s : state) (k : nat) : word :=
  let (t, v) := sorted_val_of_var k in word_of_sort s t v.

Fixpoint word_of_exp (s : state) (e : exp) : word :=
  match e with
    | Var k => word_of_var s k
    | Reg k => reg_content s m k
    | Word w => w
    | Flag n => bit n (cpsr s)
    | Bit n k => bit n (reg_content s m k)
    | If be e1 e2 =>
      if bool_of_bexp s be then word_of_exp s e1 else word_of_exp s e2
    | Add e1 e2 => add (word_of_exp s e1) (word_of_exp s e2)
    | CarryFrom_add2 e1 e2 =>
      Functions.CarryFrom_add2 (word_of_exp s e1) (word_of_exp s e2)
    | OverflowFrom_add2 e1 e2 =>
      Functions.OverflowFrom_add2 (word_of_exp s e1) (word_of_exp s e2)
    | CarryFrom_add3 e1 e2 e3 => Functions.CarryFrom_add3
      (word_of_exp s e1) (word_of_exp s e2) (word_of_exp s e3)
    | OverflowFrom_add3 e1 e2 e3 => Functions.OverflowFrom_add3
      (word_of_exp s e1) (word_of_exp s e2) (word_of_exp s e3)
  end

with bool_of_bexp (s : state) (be : bexp) : bool :=
  match be with
    | Eq e1 e2 => zeq (word_of_exp s e1) (word_of_exp s e2)
    | CurrentModeHasSPSR => Functions.CurrentModeHasSPSR m
  end.

(****************************************************************************)
(** Semantics of pseudo-code instructions *)
(****************************************************************************)

Definition update (le : lexp) (w : word) (s : state) : bool * state :=
  match le with
    | LCPSR => (true, update_cpsr w s)
    | LReg k => (zne k 15, update_reg m k w s)
    | LFlag n => (true, update_cpsr (update n w (cpsr s)) s)
  end.

Fixpoint interp (i : inst) (s : state) : result :=
  match i with
    | Unpredictable => None
    | Seq i1 i2 =>
      match interp i1 s with
        | None => None
        | Some (b1, s1) =>
          match interp i2 s1 with
            | None => None
            | Some (b2, s2) => Some (andb b1 b2, s2)
          end
      end
    | Affect le e => Some (update le (word_of_exp s e) s)
    | IfThen be i => if bool_of_bexp s be then interp i s else Some (true, s)
    | IfThenElse be i1 i2 =>
      if bool_of_bexp s be then interp i1 s else interp i2 s
    | Affect_CPSR_SPSR =>
      match m with
        | exn e => Some (true, update_cpsr (spsr s e) s)
        | _ => None
      end
  end.

End interp.
