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
Require Import List.
Require Import ZArith.
Require Import Integers. Import Int.
Require Import Shift.
Require Import State.

(****************************************************************************)
(** Table A3-1 Condition codes (p. 112) *)
(****************************************************************************)

Fixpoint condition (w : word) :=
  match bits_val 31 28 w with
    | 0 => EQ
    | 1 => NE
    | 2 => CS
    | 3 => CC
    | 4 => MI
    | 5 => PL
    | 6 => VS
    | 7 => VC
    | 8 => HI
    | 9 => LS
    | 10 => GE
    | 11 => LT
    | 12 => GT
    | 13 => LE
    | 14 => AL
    | _ => UN
  end.

(****************************************************************************)
(** instruction decoding *)
(****************************************************************************)

Section clist.

Variables (A : Type) (a : A).

Fixpoint clist (k : nat) : list A :=
  match k with
    | O => nil
    | S k' => a :: clist k'
  end.

End clist.

Local Notation "0" := false.
Local Notation "1" := true.
Local Infix "'" := cons (at level 60, right associativity).

Fixpoint bools_of_positive (p : positive) (acc : list bool) : list bool :=
  match p with
    | xI p' => bools_of_positive p' (0'acc)
    | xO p' => bools_of_positive p' (1'acc)
    | xH => 1'acc
  end.

Definition bools_of_word (w : word) : list bool :=
  match unsigned w with
    | Zpos p => bools_of_positive p nil
    | _ => clist 0 wordsize
  end.

(*REMOVE: to be automatically generated

Inductive decode_result : Type :=
  Inst (i : instruction) | Undefined | Unpredictable.

Definition decode (w : word) : decode_result :=
  match bools_of_word w with
   (* A4.1.2 ADC (p. 154) *)
   (*31 30 29 28 27 26 25 24 23 22 21 20 19 18 17 16 15 14 13 12 10 09 08 07 06 05 04 03 02 01*)
    | _ '_ '_ '_ '0 '0 'i '0 '1 '0 '1 's '_ '_ '_ '_ '_ '_ '_ '_ '_ '_ '_ 'x '_ '_ 'y '_ '_ '_ '_ =>
      (*FIXME: only if [negb (negb i && x && y)] *)
      Inst (ADC (condition w) s (reg_num_from_bit 12 w) (reg_num_from_bit 16 w) (decode_shifter_operand w i y))
   (* A4.1.3 ADD (p. 156) *)
   (*31 30 29 28 27 26 25 24 23 22 21 20 19 18 17 16 15 14 13 12 10 09 08 07 06 05 04 03 02 01*)
    | _ '_ '_ '_ '0 '0 'i '0 '1 '0 '0 's '_ '_ '_ '_ '_ '_ '_ '_ '_ '_ '_ 'x '_ '_ 'y '_ '_ '_ '_ =>
      (*FIXME: only if [negb (negb i && x && y)] *)
      Inst (ADD (condition w) s (reg_num_from_bit 12 w) (reg_num_from_bit 16 w) (decode_shifter_operand w i y))
   (* A4.1.4 AND (p. 158) *)
   (*31 30 29 28 27 26 25 24 23 22 21 20 19 18 17 16 15 14 13 12 10 09 08 07 06 05 04 03 02 01*)
    | _ '_ '_ '_ '0 '0 'i '0 '0 '0 '0 's '_ '_ '_ '_ '_ '_ '_ '_ '_ '_ '_ 'x '_ '_ 'y '_ '_ '_ '_ =>
      (*FIXME: only if [negb (negb i && x && y)] *)
      Inst (AND (condition w) s (reg_num_from_bit 12 w) (reg_num_from_bit 16 w) (decode_shifter_operand w i y))
    | _ => Unpredictable (*FIXME*)
  end.
*)
