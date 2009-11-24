(**
SimSoC-Cert, a Coq library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Instruction decoding.
*)

Set Implicit Arguments.

Require Import Bitvec.
Require Import Instructions.
Require Import List.
Require Import ZArith.
Require Import Integers. Import Int.
Require Import Shift.
Require Import State.

Section clist.

Variables (A : Type) (a : A).

Fixpoint clist (k : nat) : list A :=
  match k with
    | O => nil
    | S k' => a :: clist k'
  end.

End clist.

Fixpoint bools_of_positive (p : positive) (acc : list bool) : list bool :=
  match p with
    | xI p' => bools_of_positive p' (false :: acc)
    | xO p' => bools_of_positive p' (true :: acc)
    | xH => true :: acc
  end.

Definition bools_of_word (w : word) : list bool :=
  match unsigned w with
    | Zpos p => bools_of_positive p nil
    | _ => clist false wordsize
  end.

Section decode.

Local Notation "0" := false.
Local Notation "1" := true.
Local Infix "'" := cons (at level 60, right associativity).

Definition decode (w : word) : option instruction :=
  match bools_of_word w with
   (* A4.1.2 ADC (p. 154) *)
   (*31 30 29 28 27 26 25 24 23 22 21 20 19 18 17 16 15 14 13 12 10 09 08 07 06 05 04 03 02 01*)
    | _ '_ '_ '_ '0 '0 'i '0 '1 '0 '1 's '_ '_ '_ '_ '_ '_ '_ '_ '_ '_ '_ 'x '_ '_ 'y '_ '_ '_ '_ =>
      (*FIXME: only if [negb (negb i && x && y)] *)
      Some (ADC s (reg_num_of 12 w) (reg_num_of 16 w) (decode_shifter_operand w i y))
   (* A4.1.3 ADD (p. 156) *)
   (*31 30 29 28 27 26 25 24 23 22 21 20 19 18 17 16 15 14 13 12 10 09 08 07 06 05 04 03 02 01*)
    | _ '_ '_ '_ '0 '0 'i '0 '1 '0 '0 's '_ '_ '_ '_ '_ '_ '_ '_ '_ '_ '_ 'x '_ '_ 'y '_ '_ '_ '_ =>
      (*FIXME: only if [negb (negb i && x && y)] *)
      Some (ADD s (reg_num_of 12 w) (reg_num_of 16 w) (decode_shifter_operand w i y))
   (* A4.1.4 AND (p. 158) *)
   (*31 30 29 28 27 26 25 24 23 22 21 20 19 18 17 16 15 14 13 12 10 09 08 07 06 05 04 03 02 01*)
    | _ '_ '_ '_ '0 '0 'i '0 '0 '0 '0 's '_ '_ '_ '_ '_ '_ '_ '_ '_ '_ '_ 'x '_ '_ 'y '_ '_ '_ '_ =>
      (*FIXME: only if [negb (negb i && x && y)] *)
      Some (AND s (reg_num_of 12 w) (reg_num_of 16 w) (decode_shifter_operand w i y))
    | _ => None (*FIXME*)
  end.

End decode.
