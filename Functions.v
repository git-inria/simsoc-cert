(**
SimSoC-Cert, a Coq library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Pseudocode functions.
*)

Set Implicit Arguments.

Require Import Util.
Require Import Bitvec.
Require Import Integers. Import Int.
Require Import State.
Require Import Coqlib.

(****************************************************************************)
(** Logical_Shift_Left (p. 1129) *)
(****************************************************************************)

(* Performs a left shift, inserting zeros in the vacated bit positions
on the right. *)

Definition Logical_Shift_Left := shl. (*FIXME?*)

(****************************************************************************)
(** Logical_Shift_Right (p. 1129) *)
(****************************************************************************)

(* Performs a right shift, inserting zeros in the vacated bit
positions on the left. *)

Definition Logical_Shift_Right := shru. (*FIXME?*)

(****************************************************************************)
(** Arithmetic_Shift_Right (p. 1121) *)
(****************************************************************************)

(* Performs a right shift, repeatedly inserting the original left-most
bit (the sign bit) in the vacated bit positions on the left. *)

Definition Arithmetic_Shift_Right := shr. (*FIXME?*)

(****************************************************************************)
(** Rotate_Right (p. 1132) *)
(****************************************************************************)

(* Performs a right rotate, where each bit that is shifted off the
right is inserted on the left. *)

Definition Rotate_Right := ror. (*FIXME?*)

(****************************************************************************)
(** SignExtend(arg) (p.1134) *)
(****************************************************************************)

(* Sign-extends (propagates the sign bit) its argument to 32 bits. *)

Definition SignExtend := sign_ext. (*FIXME?*)

(****************************************************************************)
(** CurrentModeHasSPSR (p. 1125) *)
(****************************************************************************)

(* Returns TRUE if the current processor mode is not User mode or
System mode, and returns FALSE if the current mode is User mode or
System mode. *)

Definition CurrentModeHasSPSR (m : processor_mode) : bool :=
  match m with
    | usr | sys => false
    | _ => true
  end.

(****************************************************************************)
(** CarryFrom (p. 1124) *)
(****************************************************************************)

(* Returns 1 if the addition specified as its parameter caused a carry
(true result is bigger than 2^32-1, where the operands are treated as
unsigned integers), and returns 0 in all other cases. This delivers
further information about an addition which occurred earlier in the
pseudo-code. The addition is not repeated. *)

Definition CarryFrom_add2 (x y : word) : word :=
  word_of_bool (zlt max_unsigned (unsigned x + unsigned y)).

Definition CarryFrom_add3 (x y z : word) : word :=
  word_of_bool (zlt max_unsigned (unsigned x + unsigned y + unsigned z)).

(****************************************************************************)
(** OverflowFrom (p. 1131) *)
(****************************************************************************)

(* Returns 1 if the addition or subtraction specified as its parameter
caused a 32-bit signed overflow. Addition generates an overflow if
both operands have the same sign (bit[31]), and the sign of the result
is different to the sign of both operands. Subtraction causes an
overflow if the operands have different signs, and the first operand
and the result have different signs.  This delivers further
information about an addition or subtraction which occurred earlier in
the pseudo-code.  The addition or subtraction is not repeated. *)

Definition OverflowFrom_add2 (x y : word) : word :=
  word_of_bool (zlt max_signed (signed x + signed y)).

(*IMPROVE: use this more efficient definition given p. 1131?*)
Definition OverflowFrom_add2' (x y : word) (r : word) :=
  let sx := is_neg x in (eqb sx (is_neg y)) && (bne sx (is_neg r)).

Definition OverflowFrom_add3 (x y z : word) : word :=
  word_of_bool (zlt max_signed (signed x + signed y + signed z)).

(****************************************************************************)
(** A3.2 The condition field (p. 111) *)
(****************************************************************************)

Definition ConditionPassed (w : word) : bool :=
  match bits_val 31 28 w with
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
