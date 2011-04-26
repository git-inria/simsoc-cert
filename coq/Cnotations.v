(**
SimSoC-Cert, a toolkit for generating certified processor simulators.

See the COPYRIGHTS and LICENSE files.

Notations and coercions for C programs.
*)

Set Implicit Arguments.

Require Import List BinInt String.
Require Export Integers AST Values Csyntax Ascii.

(****************************************************************************)
(** notations for Coq data structures *)

Notation "[ ]" := nil.
Notation "[ a ; .. ; b ]" := (a :: .. (b :: nil) ..).

(****************************************************************************)
(** convert Coq strings into lists of Values.init_data *)

Definition init_data_of_ascii a := Init_int8 (Int.repr (Z_of_N (N_of_ascii a))).

Definition list_init_data_of_list_ascii := List.map init_data_of_ascii.

Fixpoint list_init_data_of_string s :=
  match s with
    | EmptyString => []
    | String a s => init_data_of_ascii a :: list_init_data_of_string s
  end.

Definition null_termin_string s := (s ++ String "000" "")%string.

(****************************************************************************)
(** coercions *)

Coercion Int.repr : Z >-> int.
Coercion Vint : int >-> val.
Coercion Sdo : expr >-> statement.
Coercion init_data_of_ascii : ascii >-> init_data.
Coercion list_init_data_of_string : string >-> list.

(****************************************************************************)
(* notations *)

Notation "a -: b" := (pair a b) (at level 60).

Notation "` x" := (Int.repr x) (at level 9).
Notation "`` x" := (Init_int8 ` x) (at level 9).

Notation int8 := (Tint I8 Signed).
Notation uint8 := (Tint I8 Unsigned).
Notation int16 := (Tint I16 Signed).
Notation uint16 := (Tint I16 Unsigned).
Notation int32 := (Tint I32 Signed).
Notation uint32 := (Tint I32 Unsigned).
Notation float32 := (Tfloat F32).
Notation float64 := (Tfloat F64).

Notation void := Tvoid.
Notation "`*` t" := (Tpointer t) (at level 20).

Notation "a :T: b" := (Tcons a b) (at level 70, right associativity).
Notation "T[ ]" := Tnil.
Notation "T[ a ; .. ; b ]" := (a :T: .. (b :T: Tnil) ..).

Definition fcons a := Fcons (fst a) (snd a).
Notation "a :F: b" := (fcons a b) (at level 70, right associativity).
Notation "F[ ]" := Fnil.
Notation "F[ a ; .. ; b ]" := (a :F: .. (b :F: Fnil) ..).

Notation "a :E: b" := (Econs a b) (at level 70, right associativity).
Notation "E[ ]" := Enil.
Notation "E[ a ; .. ; b ]" := (a :E: .. (b :E: Enil) ..).

Notation "! x `: t" := (Eunop Onotbool x t) (at level 10).
Notation "`~ x `: t" := (Eunop Onotint x t) (at level 10).
Notation "`- x `: t" := (Eunop Oneg x t) (at level 10).

Notation "x + y `: t" := (Ebinop Oadd x y t) (at level 20).
Notation "x - y `: t" := (Ebinop Osub x y t) (at level 20).
Notation "x * y `: t" := (Ebinop Omul x y t) (at level 20).
Notation "x / y `: t" := (Ebinop Odiv x y t) (at level 20).
Notation "x % y `: t" := (Ebinop Omod x y t) (at level 20).
Notation "x & y `: t" := (Ebinop Oand x y t) (at level 20).
Notation "x `| y `: t" := (Ebinop Oor x y t) (at level 20).
Notation "x ^ y `: t" := (Ebinop Oxor x y t) (at level 20).
Notation "x << y `: t" := (Ebinop Oshl x y t) (at level 20).
Notation "x >> y `: t" := (Ebinop Oshr x y t) (at level 20).

Notation "x == y `: t" := (Ebinop Oeq x y t) (at level 20).
Notation "x != y `: t" := (Ebinop One x y t) (at level 20).
Notation "x < y `: t" := (Ebinop Olt x y t) (at level 20).
Notation "x > y `: t" := (Ebinop Ogt x y t) (at level 20).
Notation "x <= y `: t" := (Ebinop Ole x y t) (at level 20).
Notation "x >= y `: t" := (Ebinop Oge x y t) (at level 20).

Notation "x += y `: t1 `: t2" := (Eassignop Oadd x y t1 t2) (at level 8).
Notation "x -= y `: t1 `: t2" := (Eassignop Osub x y t1 t2) (at level 8).
Notation "x *= y `: t1 `: t2" := (Eassignop Omul x y t1 t2) (at level 8).
Notation "x /= y `: t1 `: t2" := (Eassignop Odiv x y t1 t2) (at level 8).
Notation "x %= y `: t1 `: t2" := (Eassignop Omod x y t1 t2) (at level 8).
Notation "x &= y `: t1 `: t2" := (Eassignop Oand x y t1 t2) (at level 8).
Notation "x `|= y `: t1 `: t2" := (Eassignop Oor x y t1 t2) (at level 8).
Notation "x ^= y `: t1 `: t2" := (Eassignop Oxor x y t1 t2) (at level 8).
Notation "x <<= y `: t1 `: t2" := (Eassignop Oshl x y t1 t2) (at level 8).
Notation "x >>= y `: t1 `: t2" := (Eassignop Oshr x y t1 t2) (at level 8).

Notation "`* e `: t" := (Ederef e t) (at level 20).
Notation "# v `: t" := (Eval v t) (at level 20).
Notation "$ id `: t" := (Evar id t) (at level 20).
Notation "\ id `: t" := (Evalof (Evar id t) t) (at level 20).
Notation "& e `: t" := (Eaddrof e t) (at level 20).
Notation "e1 ? e2 `: e3 `: t" := (Econdition e1 e2 e3 t) (at level 20).
Notation "e -- `: t" := (Epostincr Decr e t) (at level 20).
Notation "e ++ `: t" := (Epostincr Incr e t) (at level 20).
Notation "e1 `= e2 `: t" := (Eassign e1 e2 t) (at level 8).
Notation "e | id `: t" := (Efield e id t) (at level 20).
Notation "'call'" := (Ecall).
Notation "'sizeof'" := (Esizeof).
Notation "'valof'" := (Evalof).

Notation "a ;; b" := (Ssequence a b) (at level 51, right associativity).
Notation "`if a 'then' b 'else' c" := (Sifthenelse a b c) (at level 9).
Notation "'while' a `do b" := (Swhile a b) (at level 19).
Notation "`do a 'while' b" := (Sdowhile b a) (at level 19).
Notation "'label' l `: s" := (Slabel l s) (at level 5).
Notation "'for' ( s1 , e , s2 ) { s3 }" := (Sfor s1 e s2 s3) (at level 19).

Notation "'return'" := (Sreturn).
Notation "'goto'" := (Sgoto).
Notation "'continue'" := (Scontinue).
Notation "'break'" := (Sbreak).
Notation "'skip'" := (Sskip).
Notation "'switch'" := (Sswitch).

Notation "`case i `: s :L: ls" := (LScase i s ls) (at level 70).
Notation "'default' `: s" := (LSdefault s) (at level 80).
