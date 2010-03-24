(**
SimSoC-Cert, a Coq library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

.
*)

Require Import Bitvec.
Require Import State.
Require Import ZArith.
Require Import Integers. Import Int.
Require Import Coqlib.
Require Import Util.

Open Scope Z_scope.

Section IntOp.

Variable b : bool.
Variable s : state.

Definition affect_reg (n : reg_num) (w : word)
  : result :=
     Some(zne n 15, update_reg n w s).

Definition affect_cpsr (w : word)
  : result := 
  Some(b, update_cpsr w s).

Definition affect_cpsr_bit (n : nat) (v w : word)
  : result :=
  Some(b, update_cpsr (update_bit n v w) s).

Inductive instr : Type :=
| Unpredictable
| IntBlock (i1 i2 : instr)
| Affect_reg (n : reg_num) (w : word)
| Affect_cpsr (w : word)
| Affect_cpsr_bit (n : nat) (v : word) (w : word)
| IntIf (b : bool) (i : instr)
| IntIfElse (b : bool) (i1 i2 : instr)
| Affect_CPSR_SPSR.

Fixpoint intOp (i : instr) : result :=
  match i with
    | Unpredictable => None
    | IntIf b i => 
      if b then intOp i else Some(true, s)
    | IntIfElse b i1 i2 => 
      if b then intOp i1 else intOp i2
    | IntBlock i1 i2 =>
      match intOp i1 with
        | None => None
        | Some(b1, s1) =>
          match intOp i2 with
            | None =>  None
            | Some (b2, s2) => Some(andb b1 b2, s2)
          end
      end
    | Affect_reg n w => affect_reg n w
    | Affect_cpsr w => affect_cpsr w
    | Affect_cpsr_bit n v w => affect_cpsr_bit n v w
    | Affect_CPSR_SPSR =>
      match pm s with
        | exn e => Some(true, update_cpsr (spsr s e) s)
        | _ => None
      end
  end.

End IntOp.
