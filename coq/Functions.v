(**
SimSoC-Cert, a Coq library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Functions used in the pseudocode, in alphabetical order.
*)

Set Implicit Arguments.

Require Import Coqlib Integers Util Bitvec Arm.
Import Int.

(****************************************************************************)
(** Table A4-1 Bit mask constants (p. 227) *)

Definition UnallocMask : word := repr 116456448. (*FIXME*)
Definition UserMask : word := repr 4161733120.
Definition PrivMask : word := repr 479.
Definition StateMask : word := repr 16777248.

(****************************************************************************)
(** Arithmetic_Shift_Right (p. 1121)

Performs a right shift, repeatedly inserting the original left-most
bit (the sign bit) in the vacated bit positions on the left. *)
(****************************************************************************)

Definition Arithmetic_Shift_Right := shr. (*FIXME?*)

(****************************************************************************)
(** bit position of most significant '1' (p. 175) *)
(****************************************************************************)

Definition bit_position_of_most_significant_1 (w : word) : word :=
  w0. (*FIXME*)

(****************************************************************************)
(** BorrowFrom (p. 1131)

Returns 1 if the subtraction specified as its parameter caused a borrow 
(the true result is less than 0, where the operands are treated as unsigned
integers), and returns 0 in all other cases. This delivers further
information about a subtraction which occurred earlier in the pseudo-code.
The subtraction is not repeated. *)
(****************************************************************************)

Definition BorrowFrom_sub2 (x y : word) : bool :=
  zlt (unsigned x - unsigned y) 0.

Definition BorrowFrom_sub3 (x y z : word) : bool :=
  zlt (unsigned x - unsigned y - unsigned z) 0.

(****************************************************************************)
(** CarryFrom (p. 1124)

Returns 1 if the addition specified as its parameter caused a carry
(true result is bigger than 2^32-1, where the operands are treated as
unsigned integers), and returns 0 in all other cases. This delivers
further information about an addition which occurred earlier in the
pseudo-code. The addition is not repeated. *)
(****************************************************************************)

Definition CarryFrom_add2 (x y : word) : bool :=
  zlt max_unsigned (unsigned x + unsigned y).

Definition CarryFrom_add3 (x y z : word) : bool :=
  zlt max_unsigned (unsigned x + unsigned y + unsigned z).

(****************************************************************************)
(** CarryFrom (p. 1124)

Returns 1 if the addition specified as its parameter caused a carry 
(true result is bigger than 2^8−1, where the operands are treated as
unsigned integers), and returns 0 in all other cases. This delivers further
information about an addition which occurred earlier in the pseudo-code.
The addition is not repeated. *)
(****************************************************************************)

Definition CarryFrom8_add2 (x y : word) : bool :=
  zlt (two_power_nat 8 - 1) (unsigned x + unsigned y).

(****************************************************************************)
(** CarryFrom16 (p. 1124)

Returns 1 if the addition specified as its parameter caused a carry 
(true result is bigger than 2^16−1, where the operands are treated as
unsigned integers), and returns 0 in all other cases. This delivers further
information about an addition which occurred earlier in the pseudo-code.
The addition is not repeated. *)
(****************************************************************************)

Definition CarryFrom16_add2 (x y : word) : bool :=
  zlt (two_power_nat 16 - 1) (unsigned x + unsigned y).

(****************************************************************************)
(** ConditionPassed (p. 1124)

Returns TRUE if the state of the N, Z, C and V flags fulfils the
condition encoded in the cond argument, and returns FALSE in all other
cases.

A3.2 The condition field (p. 111) *)
(****************************************************************************)

Definition ConditionPassed (w : word) : bool :=
  match condition w with
    | EQ => (* Z set *) is_set Zbit w
    | NE => (* Z clear *) negb (is_set Zbit w)
    | CS => (* C set *) is_set Cbit w
    | CC => (* C clear *) negb (is_set Cbit w)
    | MI => (* N set *) is_set Cbit w
    | PL => (* N clear *) negb (is_set Cbit w)
    | VS => (* V set *) is_set Vbit w
    | VC => (* V clear *) negb (is_set Vbit w)
    | HI => (* C set and Z clear *)
      andb (is_set Cbit w) (negb (is_set Zbit w))
    | LS => (* C clear or Z set *)
      orb (negb (is_set Cbit w)) (is_set Zbit w)
    | GE => (* N set and V set, or N clear and V clear (N==V) *)
      beq (is_set Nbit w) (is_set Vbit w)
    | LT => (* N set and V clear, or N clear and V set (N!=V) *)
      negb (beq (is_set Nbit w) (is_set Vbit w))
    | GT => (* Z clear, and either N set and V set,
         or N clear and V clear (Z==0,N==V) *)
      andb (negb (is_set Zbit w)) (beq (is_set Nbit w) (is_set Vbit w))
    | LE => (* Z set, or N set and V clear, or N clear and V set
         (Z==1 or N!=V) *)
      orb (is_set Zbit w) (negb (beq (is_set Nbit w) (is_set Vbit w)))
    | AL => true
    | UN => true
  end.

(****************************************************************************)
(** CurrentModeHasSPSR (p. 1125)

Returns TRUE if the current processor mode is not User mode or
System mode, and returns FALSE if the current mode is User mode or
System mode. *)
(****************************************************************************)

Definition CurrentModeHasSPSR (m : proc_mode) : bool :=
  match m with
    | usr | sys => false
    |_ => true
  end.

(****************************************************************************)
(** InAPrivilegedMode() (p. 1128)

Returns TRUE if the current processor mode is not User mode, 
and returns FALSE if the current mode is User mode. *)
(****************************************************************************)

Definition InAPrivilegedMode (m : proc_mode) : bool :=
  match m with
    | usr => true
    | _ => false
  end.

(****************************************************************************)
(** Logical_Shift_Left (p. 1129)

Performs a left shift, inserting zeros in the vacated bit positions
on the right. *)
(****************************************************************************)

Definition Logical_Shift_Left := shl. (*FIXME?*)

(****************************************************************************)
(** Logical_Shift_Right (p. 1129)

Performs a right shift, inserting zeros in the vacated bit
positions on the left. *)
(****************************************************************************)

Definition Logical_Shift_Right := shru. (*FIXME?*)

(****************************************************************************)
(** OverflowFrom (p. 1131)

Returns 1 if the addition or subtraction specified as its parameter
caused a 32-bit signed overflow. Addition generates an overflow if
both operands have the same sign (bit[31]), and the sign of the result
is different to the sign of both operands. Subtraction causes an
overflow if the operands have different signs, and the first operand
and the result have different signs.  This delivers further
information about an addition or subtraction which occurred earlier in
the pseudo-code.  The addition or subtraction is not repeated. *)
(****************************************************************************)

Definition OverflowFrom_add2 (x y : word) : bool :=
  let r := signed x + signed y in
    orb (zlt r min_signed) (zgt r max_signed).

(*IMPROVE: use this more efficient definition given p. 1131?*)
Definition OverflowFrom_add2' (x y : word) (r : word) : bool :=
  let sx := is_neg x in (beq sx (is_neg y)) && (bne sx (is_neg r)).

Definition OverflowFrom_add3 (x y z : word) : bool :=
  let r := signed x + signed y + signed z in
    orb (zlt r min_signed) (zgt r max_signed).

Definition OverflowFrom_sub2 (x y : word) : bool :=
  let r := signed x - signed y in
    orb (zlt r min_signed) (zgt r max_signed).

Definition OverflowFrom_sub3 (x y z : word) : bool :=
  let r := signed x - signed y - signed z in
    orb (zlt r min_signed) (zgt r max_signed).

(****************************************************************************)
(** Rotate_Right (p. 1132)

Performs a right rotate, where each bit that is shifted off the
right is inserted on the left. *)
(****************************************************************************)

Definition Rotate_Right := ror. (*FIXME?*)

(****************************************************************************)
(** SignedDoesSat(x,n) (p. 1134)

Returns 0 if x lies inside the range of an n-bit signed integer (that is,
if –2(n–1) ≤ x ≤ 2(n–1) – 1), and 1 otherwise.
This operation delivers further information about a SignedSat(x, n) 
operation which occurred earlier in the pseudo-code. 
Any operations used to calculate x or n are not repeated. *)
(****************************************************************************)

Definition SignedDoesSat (x : word) (m : word) : bool :=
  let n := nat_of_Z m in
  let c1 := cmp Cge x (neg (repr (two_power_nat (n - 1)))) in
  let c2 := cmp Cle x (repr (two_power_nat n - 1)) in
    andb c1 c2.

Definition SignedDoesSat_add32 x y := SignedDoesSat (add x y) w32.
Definition SignedDoesSat_sub32 x y := SignedDoesSat (sub x y) w32.
Definition SignedDoesSat_double32 x := SignedDoesSat (mul x x) w32.

(****************************************************************************)
(** SignExtend(arg) (p. 1134)

Sign-extends (propagates the sign bit) its argument to 32 bits. *)
(****************************************************************************)

Definition SignExtend := sign_ext 32. (*FIXME?*)

Definition SignExtend_24to30 := sign_ext 24. (*FIXME?*)

(****************************************************************************)
(** SignedSat(x,n) (p. 1134)

Returns x saturated to the range of an n-bit signed integer. That is,
 it returns:
–2^(n–1)  if             x < –2^(n–1)
x         if –2^(n–1) <= x <= 2^(n–1)–1
2^(n–1)–1 if             x > 2^(n–1)–1 *)
(****************************************************************************)

Definition SignedSat (x : word) (m : word) : word :=
  let t := two_power_nat (nat_of_Z m - 1) in
  let u := neg (repr t) in
    if cmp Clt x u then u
    else let v := repr (t - 1) in
      if cmp Cgt x v then v
      else x.

Definition SignedSat_add8 x y := SignedSat (add x y) w8.
Definition SignedSat_sub8 x y := SignedSat (sub x y) w8.
Definition SignedSat_add16 x y := SignedSat (add x y) w16.
Definition SignedSat_sub16 x y := SignedSat (sub x y) w16.
Definition SignedSat_add32 x y := SignedSat (add x y) w32.
Definition SignedSat_double32 x := SignedSat (mul x x) w32.
Definition SignedSat_sub32 x y := SignedSat (sub x y) w32.

(****************************************************************************)
(** UnSignedDoesSat(x,n) (p. 1136)

Returns 0 if x lies within the range of an n-bit unsigned integer (that is, 
if 0 ≤ x < 2^n) and 1 otherwise. This operation delivers further information 
about an UnsignedSat(x,n) operation that occurred earlier in the pseudo-code. 
Any operations used to calculate x or n are not repeated. *)
(****************************************************************************)

Definition UnsignedDoesSat (x : word) (m : word) : bool :=
  let c1 := cmp Cge x w0 in
  let c2 := cmp Clt x (repr (two_power_nat (nat_of_Z m))) in
    andb c1 c2.

(****************************************************************************)
(** UnsignedSat(x,n) (p. 1136)

Returns x saturated to the range of an n-bit unsigned integer. That is,
 it returns:
0     if      x < 0
x     if 0 <= x < 2^n
2^n–1 if      x > 2^n – 1 *)
(****************************************************************************)

Definition UnsignedSat (x : word) (m : word) : word :=
  if cmp Clt x w0 then w0
  else let t := repr (two_power_nat (nat_of_Z m) - 1) in
    if cmp Clt x t then x
    else t.

Definition UnsignedSat_add32 x y := UnsignedSat (add x y) w32.
Definition UnsignedSat_add16 x y := UnsignedSat (add x y) w16.
Definition UnsignedSat_add8 x y := UnsignedSat (add x y) w8.
Definition UnsignedSat_sub32 x y := UnsignedSat (sub x y) w32.
Definition UnsignedSat_sub16 x y := UnsignedSat (sub x y) w16.
Definition UnsignedSat_sub8 x y := UnsignedSat (sub x y) w8.

(****************************************************************************)
(** ZeroExtend

Not defined in the Glossary, occurs in the pseudo-code for LDRH
(p. 205), USAD8 (p. 412), USADA8 (p. 414), LDRH(1) (p. 573), LDRH(2)
(p. 575). *)
(****************************************************************************)

Definition ZeroExtend := zero_ext 32. (*FIXME?*)
