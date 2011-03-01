Require Import Coqlib.
Require Import Integers.
Require Import Floats.
Require Import AST.
Require Import Csyntax.


Module Rec.
(** This module gives a destructor for each local type used to build the main type [Csyntax.program].
Each declared function [_f] behaves approximatively as its [f_rect], except that mutually functions are handled using the 'Scheme' command, and if we are dealing with a recursive type, the recursive call is done implicitly. *)

Definition _option {A B C} (a : _ -> C) f := @option_rect A (fun _ => B) (fun x => f (a x)).

Definition _positive {A} f f0 := @positive_rect (fun _ => A) (fun _ x => f x) (fun _ x => f0 x).

Definition _Z {A POSITIVE}
  (_positive : _ -> POSITIVE)
  f_zero f_pos f_neg
  := 
  Z_rect (fun _ => A)
  f_zero
  (fun x => f_pos (_positive x))
  (fun x => f_neg (_positive x)).

Definition _list {A B E} (a : A -> B) fn (fc : _ -> E -> _) :=
  @list_rect A _ fn (fun x _ aux_xs => fc (a x) aux_xs).

Definition _prod {A0 A1 B0 B1 C} (a : A0 -> A1) (b : B0 -> B1) f := prod_rect (fun _ => C) 
  (fun va vb => f (a va) (b vb)).

Definition _ident {A} := @_positive A.

Definition _init_data {A B C D E} 
  (_int : _ -> B) (_float : _ -> C) (_Z : _ -> D) (_ident : _ -> E) 
  f_i8 f_i16 f_i32 f_f32 f_f64 f_space f_addrof
  := 
  init_data_rect (fun _ => A)
  (fun x => f_i8 (_int x))
  (fun x => f_i16 (_int x))
  (fun x => f_i32 (_int x))
  (fun x => f_f32 (_float x))
  (fun x => f_f64 (_float x))
  (fun x => f_space (_Z x))
  (fun i i2 => f_addrof (_ident i) (_int i2)).

Module _AST.
Definition _program {A B D   F V : Type}
  f_prod f_ni f_co
  f_f f_v 
  _ident _init_data
  (f_mk : A -> B -> A -> D) 
  (x : _ F V)
  :=
  f_mk
    (_list (_prod _ident f_f f_prod) f_ni f_co (prog_funct x)) 
    (_ident (prog_main x)) 
    (_list (_prod (_prod _ident (_list _init_data f_ni f_co) f_prod) f_v f_prod) f_ni f_co (prog_vars x)).
End _AST.

Definition _signedness {A} := signedness_rect (fun _ => A).
Definition _intsize {A} := intsize_rect (fun _ => A).
Definition _floatsize {A} := floatsize_rect (fun _ => A).

Scheme _type_rect := Induction for type Sort Type
with _typelist_rect := Induction for typelist Sort Type
with _fieldlist_rect := Induction for fieldlist Sort Type.

Definition _ty_ AA P P0 P1 
  (f_ty : forall (P : type -> Type) (P0 : typelist -> Type)
         (P1 : fieldlist -> Type),
       P Tvoid ->
       (forall (i : intsize) (s : signedness), P (Tint i s)) ->
       (forall f1 : floatsize, P (Tfloat f1)) ->
       (forall t : type, P t -> P (Tpointer t)) ->
       (forall t : type, P t -> forall z : Z, P (Tarray t z)) ->
       (forall t : typelist,
        P0 t -> forall t0 : type, P t0 -> P (Tfunction t t0)) ->
       (forall (i : ident) (f5 : fieldlist), P1 f5 -> P (Tstruct i f5)) ->
       (forall (i : ident) (f6 : fieldlist), P1 f6 -> P (Tunion i f6)) ->
       (forall i : ident, P (Tcomp_ptr i)) ->
       P0 Tnil ->
       (forall t : type,
        P t -> forall t0 : typelist, P0 t0 -> P0 (Tcons t t0)) ->
       P1 Fnil ->
       (forall (i : ident) (t : type),
        P t -> forall f11 : fieldlist, P1 f11 -> P1 (Fcons i t f11)) ->
       AA P P0 P1)
  {A B C D E}
  (_intsize : _ -> A) (_signedness : _ -> B) (_floatsize : _ -> C) (_Z : _ -> D) (_ident : _ -> E)
  f_void f_int f_float f_pointer f_array f_function f_struct f_union f_comp_ptr   f_tnil f_tcons   f_fnil f_fcons
  := f_ty (fun _ => P) (fun _ => P0) (fun _ => P1)
    f_void
    (fun i s => f_int (_intsize i) (_signedness s))
    (fun f => f_float (_floatsize f))
    (fun _ aux => f_pointer aux)
    (fun _ aux z => f_array aux (_Z z))
    (fun _ aux0 _ aux1 => f_function aux0 aux1)
    (fun i _ aux => f_struct (_ident i) aux)
    (fun i _ aux => f_union (_ident i) aux)
    (fun i => f_comp_ptr (_ident i))

    f_tnil
    (fun _ aux1 _ aux2 => f_tcons aux1 aux2)

    f_fnil
    (fun i _ aux1 _ aux2 => f_fcons (_ident i) aux1 aux2)
.

Definition _type {P P0 P1} := @_ty_ _ P P0 P1 _type_rect.
Definition _typelist {P P0 P1} := @_ty_ _ P P0 P1 _typelist_rect.
Definition _fieldlist {P P0 P1} := @_ty_ _ P P0 P1 _fieldlist_rect.

Definition _unary_operation {A} := unary_operation_rect (fun _ => A).
Definition _binary_operation {A} := binary_operation_rect (fun _ => A).

Scheme _expr_rect := Induction for expr Sort Type
with _expr_descr_rect := Induction for expr_descr Sort Type.

Definition _expr_ A P P0
  (_expr_ : forall (P : expr -> Type) (P0 : expr_descr -> Type),
       (forall e : expr_descr, P0 e -> forall t : type, P (Expr e t)) ->
       (forall i : int, P0 (Econst_int i)) ->
       (forall f1 : float, P0 (Econst_float f1)) ->
       (forall i : ident, P0 (Evar i)) ->
       (forall e : expr, P e -> P0 (Ederef e)) ->
       (forall e : expr, P e -> P0 (Eaddrof e)) ->
       (forall (u : unary_operation) (e : expr), P e -> P0 (Eunop u e)) ->
       (forall (b : binary_operation) (e : expr),
        P e -> forall e0 : expr, P e0 -> P0 (Ebinop b e e0)) ->
       (forall (t : type) (e : expr), P e -> P0 (Ecast t e)) ->
       (forall e : expr,
        P e ->
        forall e0 : expr,
        P e0 -> forall e1 : expr, P e1 -> P0 (Econdition e e0 e1)) ->
       (forall e : expr, P e -> forall e0 : expr, P e0 -> P0 (Eandbool e e0)) ->
       (forall e : expr, P e -> forall e0 : expr, P e0 -> P0 (Eorbool e e0)) ->
       (forall t : type, P0 (Esizeof t)) ->
       (forall e : expr, P e -> forall i : ident, P0 (Efield e i)) ->
       A P P0)
  {INT FLOAT TYPE IDENT UNARY_OPERATION BINARY_OPERATION}
  (_float : _ -> FLOAT) (_int : _ -> INT) (_type : _ -> TYPE) (_ident : _ -> IDENT) (_unary_operation : _ -> UNARY_OPERATION) (_binary_operation : _ -> BINARY_OPERATION)
  f_expr f_const_int f_const_float f_var f_deref f_addrof f_unop f_binop f_cast f_condition f_andbool f_orbool f_sizeof f_field
  := 
  _expr_ (fun _ => P) (fun _ => P0) 

    (fun _ aux t => f_expr aux (_type t))

    (fun i => f_const_int (_int i))
    (fun f => f_const_float (_float f))
    (fun i => f_var (_ident i))
    (fun _ aux => f_deref aux)
    (fun _ aux => f_addrof aux)
    (fun u _ aux => f_unop (_unary_operation u) aux)
    (fun b _ aux1 _ aux2 => f_binop (_binary_operation b) aux1 aux2)
    (fun t _ aux => f_cast (_type t) aux)
    (fun _ aux1 _ aux2 _ aux3 => f_condition aux1 aux2 aux3)
    (fun _ aux1 _ aux2 => f_andbool aux1 aux2)
    (fun _ aux1 _ aux2 => f_orbool aux1 aux2)
    (fun t => f_sizeof (_type t))
    (fun _ aux i => f_field aux (_ident i))
.

Definition _expr {P P0} := @_expr_ _ P P0 _expr_rect.
Definition _expr_descr {P P0} := @_expr_ _ P P0 _expr_descr_rect.

Definition _label {A} := @_ident A.

Scheme _statement_rect := Induction for statement Sort Type
with _labeled_statements_rect := Induction for labeled_statements Sort Type.

Definition _statement_ A P P0 
  (_statement_ : forall (P : statement -> Type) (P0 : labeled_statements -> Type),
       P Sskip ->
       (forall e e0 : expr, P (Sassign e e0)) ->
       (forall (o : option expr) (e : expr) (l : list expr), P (Scall o e l)) ->
       (forall s : statement,
        P s -> forall s0 : statement, P s0 -> P (Ssequence s s0)) ->
       (forall (e : expr) (s : statement),
        P s -> forall s0 : statement, P s0 -> P (Sifthenelse e s s0)) ->
       (forall (e : expr) (s : statement), P s -> P (Swhile e s)) ->
       (forall (e : expr) (s : statement), P s -> P (Sdowhile e s)) ->
       (forall s : statement,
        P s ->
        forall (e : expr) (s0 : statement),
        P s0 -> forall s1 : statement, P s1 -> P (Sfor s e s0 s1)) ->
       P Sbreak ->
       P Scontinue ->
       (forall o : option expr, P (Sreturn o)) ->
       (forall (e : expr) (l : labeled_statements), P0 l -> P (Sswitch e l)) ->
       (forall (l : label) (s : statement), P s -> P (Slabel l s)) ->
       (forall l : label, P (Sgoto l)) ->
       (forall s : statement, P s -> P0 (LSdefault s)) ->
       (forall (i : int) (s : statement),
        P s -> forall l : labeled_statements, P0 l -> P0 (LScase i s l)) -> A P P0)
  { C EXPR LABEL INT OPTION }
  f_some (f_none : OPTION) (f_ni : C) f_co 
  (_expr : _ -> EXPR) (_label : _ -> LABEL) (_int : _ -> INT)
  f_skip f_assign f_call f_sequence f_ifthenelse f_while f_dowhile f_for f_break f_continue f_return f_switch f_label f_goto f_default f_case
  :=
  _statement_ (fun _ => P) (fun _ => P0) 
    f_skip
    (fun e1 e2 => f_assign (_expr e1) (_expr e2))
    (fun o e l => f_call (_option _expr f_some f_none o) (_expr e) (_list _expr f_ni f_co l))
    (fun _ aux1 _ aux2 => f_sequence aux1 aux2)
    (fun e _ aux1 _ aux2 => f_ifthenelse (_expr e) aux1 aux2)
    (fun e _ aux => f_while (_expr e) aux)
    (fun e _ aux => f_dowhile (_expr e) aux)
    (fun _ aux1 e _ aux2 _ aux3 => f_for aux1 (_expr e) aux2 aux3)
    f_break
    f_continue
    (fun o => f_return (_option _expr f_some f_none o))
    (fun e _ aux => f_switch (_expr e) aux)
    (fun l _ aux => f_label (_label l) aux)
    (fun l => f_goto (_label l))

    (fun _ aux => f_default aux)
    (fun i _ aux1 _ aux2 => f_case (_int i) aux1 aux2)
.

Definition _statement {P P0} := @_statement_ _ P P0 _statement_rect.
Definition _labeled_statements {P P0} := @_statement_ _ P P0 _labeled_statements_rect.

Definition _function { PROD LIST IDENT TYPE STATEMENT FUNCTION}
  (f_prod : _ -> _ -> PROD) (f_ni : LIST) f_co
  (_ident : _ -> IDENT) (_type : _ -> TYPE) (_statement : _ -> STATEMENT)
  (f_mk : _ -> _ -> _ -> _ -> FUNCTION) 
  x
 :=
  f_mk 
    (_type (fn_return x)) 
    (_list (_prod _ident _type f_prod) f_ni f_co (fn_params x)) 
    (_list (_prod _ident _type f_prod) f_ni f_co (fn_vars x))
    (_statement (fn_body x)).

Definition _fundef {A  FUNCTION IDENT TYPELIST TYPE}
  (_function : _ -> FUNCTION) (_ident : _ -> IDENT) (_typelist : _ -> TYPELIST) (_type : _ -> TYPE)
  f_internal f_external
 :=
  fundef_rect (fun _ => A)
  (fun x => f_internal (_function x))
  (fun i tl t => f_external (_ident i) (_typelist tl) (_type t)).
End Rec.


Module Rec_weak. 
(** For each general function inside the module [Rec], we change its type to a lower one : each polymorphic type is explicit instancitated with a single polymorphic one. 
This polymorphic information can be thought as an accumulator staying alive along the whole execution, it can be used for example with a monadic construction.
After this change, we generalize each function construction "_ -> _ -> _ -> _ -> _" to a more general one "_ ^^ _ --> _" by using the NaryFunctions library.
This is useful if we do not want to abstract manually the "fun _ => _" during the application time. 
Note that we have to give explicitely a natural number describing the arity we are considering in each case. *)
Import Rec.
Require Import NaryFunctions.
Notation "A ** n" := (A ^^ n --> A) (at level 29) : type_scope.

Definition _positive {A} :
  A ** 1 ->
  A ** 1 ->
  A ** 0 ->
  _ := @_positive _ .
Definition _Z {A} : _ ->
  A ** 0 ->
  A ** 1 ->
  A ** 1 ->
  _ := @_Z A A.
Definition _ident {A} :
  A ** 1 ->
  A ** 1 ->
  A ** 0 ->
  _ := @_ident _.
Definition _init_data {A} : _ -> _ -> _ -> _ -> 
  A ** 1 ->
  A ** 1 ->
  A ** 1 ->
  A ** 1 ->
  A ** 1 ->
  A ** 1 ->
  A ** 2 ->
  _ := @_init_data _ _ _ _ _.
Module _AST.
Definition _program {A B C} : A ** 2 -> A ** 0 -> A ** 2 -> _ -> _ -> _ -> _ ->
  A ** 3 ->
  _ := @_AST._program _ _ _ B C.
End _AST.
Definition _signedness {A} :
  A ** 0 ->
  A ** 0 ->
  _ := @_signedness _.
Definition _intsize {A} :
  A ** 0 ->
  A ** 0 ->
  A ** 0 ->
  _ := @_intsize _.
Definition _floatsize {A} :
  A ** 0 ->
  A ** 0 ->
  _ := @_floatsize _.
Definition _type_ A B (f : _ -> Type) := f (
  A ** 0 ->
  A ** 2 ->
  A ** 1 ->
  A ** 1 ->
  A ** 2 ->
  A ** 2 ->
  A ** 2 ->
  A ** 2 ->
  A ** 1 ->
  A ** 0 ->
  A ** 2 ->
  A ** 0 ->
  A ** 3 ->
  B).
Definition _type {A} : _type_ A _ (fun ty => _ -> _ -> _ -> _ -> _ -> ty) := @_type _ _ _ _ _ _ _ _.
Definition _typelist {A} : _type_ A _ (fun ty => _ -> _ -> _ -> _ -> _ -> ty) := @_typelist _ _ _ _ _ _ _ _.
Definition _unary_operation {A} : 
  A ** 0 ->
  A ** 0 ->
  A ** 0 ->
  _ := @_unary_operation _.
Definition _binary_operation {A} :
  A ** 0 ->
  A ** 0 ->
  A ** 0 ->
  A ** 0 ->
  A ** 0 ->
  A ** 0 ->
  A ** 0 ->
  A ** 0 ->
  A ** 0 ->
  A ** 0 ->
  A ** 0 ->
  A ** 0 ->
  A ** 0 ->
  A ** 0 ->
  A ** 0 ->
  A ** 0 ->
  _ := @_binary_operation _.
Definition _expr {A} : _ -> _ -> _ -> _ -> _ -> _ -> 
  A ** 2 -> 
  A ** 1 -> 
  A ** 1 -> 
  A ** 1 -> 
  A ** 1 -> 
  A ** 1 -> 
  A ** 2 -> 
  A ** 3 -> 
  A ** 2 -> 
  A ** 3 -> 
  A ** 2 -> 
  A ** 2 -> 
  A ** 1 -> 
  A ** 2 -> 
  _ := @_expr _ _ _ _ _ _ _ _.
Definition _label {A} :
  A ** 1 ->
  A ** 1 ->
  A ** 0 ->
  _ := @_label _.
Definition _statement {A} : A ** 1 -> A ** 0 -> A ** 0 -> A ** 2 -> _ -> _ -> _ -> 
  A ** 0 -> 
  A ** 2 -> 
  A ** 3 -> 
  A ** 2 -> 
  A ** 3 -> 
  A ** 2 -> 
  A ** 2 -> 
  A ** 4 -> 
  A ** 0 -> 
  A ** 0 -> 
  A ** 1 -> 
  A ** 2 -> 
  A ** 2 -> 
  A ** 1 -> 
  A ** 1 -> 
  A ** 3 -> 
  _ := @_statement _ _ _ _ _ _ _.
Definition _function {A} : A ** 2 -> A ** 0 -> A ** 2 -> _ -> _ -> _ -> 
  A ** 4 ->
  _ := @_function _ _ _ _ _ _.
Definition _fundef {A} : _ -> _ -> _ -> _ -> 
  A ** 1 ->
  A ** 3 ->
  _ := @_fundef _ _ _ _ _.

End Rec_weak.




Module Type MONAD.
  Require Import NaryFunctions String.
  Inductive list_n {A : Type} : nat -> Type :=
    | nil_n : list_n O
    | cons_n : forall n, A -> list_n n -> list_n (S n).

  Parameter t : Type -> Type.
  Parameter ret : forall A, A -> t A.
  Parameter bind : forall A B, t A -> (A -> t B) -> t B.

  Parameter _U : string -> forall n, t unit ^^ n --> t unit. (* uplet *)
  Parameter _R : forall n, @list_n string n -> t unit ^^ n --> t unit. (* record *)
  Parameter _float : (Z -> t unit) -> float -> t unit.
  Parameter _int : (Z -> t unit) -> int -> t unit.
End MONAD.

Module Monad_base <: MONAD.
Require Import NaryFunctions String.
Open Scope string_scope.

Notation "[ ]" := nil.
Notation "[ a ; .. ; b ]" := (a :: .. (b :: []) ..).

Inductive list_n {A : Type} : nat -> Type :=
  | nil_n : list_n O
  | cons_n : forall n, A -> list_n n -> list_n (S n).

(* Convert a [list_n] into a [list] with an extra property on its length. *)
Definition list_of_list_n : forall A n, @list_n A n -> { l : list A | n = List.length l }.
  induction n ; intros.
  exists nil.
  trivial.
  inversion X.
  destruct (IHn X1).
  exists (X0 :: x).
  simpl.
  auto.
Defined.

Definition st := list string.
Inductive state {A} :=
  L (_ : A) (_ : st).

Definition t A := st -> @state A.
Definition ret {A} (a : A) := L a.

Definition bind {A B} (m : t A) (f : A -> t B) : t B :=
  fun lbs0 => 
  match m lbs0 with 
    | L a lbs1 => f a lbs1
  end.

Definition next {A B} (f1 : t A) (f2 : t B) : t B :=
  bind f1 (fun _ =>  f2).

Definition perform l := 
  List.fold_left (fun acc m => next acc m) l (ret tt).

Definition push s : t unit := fun st => ret tt (s :: st).
 
Definition _U s n := 
  ncurry _ _ n
  (fun cpl =>
    List.fold_left (fun acc (m : t unit) => perform
      [ acc
      ; push " ("
      ; m
      ; push ")" ]
    ) (nprod_to_list _ _ cpl) (push s)
  ).

Definition _R n (l : @list_n string n) : t unit ^^ n --> t unit :=
  ncurry _ _ n
  (fun cpl => perform
    [ push "{| "
    ; let f pref xs :=
        fold_left (fun acc (l : string * t unit) => let (s, m) := l in perform
          [ acc
          ; push (pref ++ s ++ " := ")
          ; m ]
        ) xs (ret tt) in
      match List.combine (let (l, _) := list_of_list_n _ _ l in l) (nprod_to_list _ _ cpl) with
        | x :: xs => perform
          [ f "" [x]
          ; f " ; " xs ]
        | l => f " ; " l
      end
    ; push " |}" ]
  ).

Definition _int (_Z : _ -> t unit) i : t unit := perform
  [ push "Int.repr ("
  ; _Z (Int.intval i)
  ; push ")" ].

Definition _float _Z f := perform
  [ push "Float.floatofint ("
  ; _int _Z (Float.intoffloat f)
  ; push ")" ].

End Monad_base.

Module Mo (Import M : MONAD). 
(** The pretty-printing is done inside this module : for each type, we explicitly write the name of the corresponding constructor inside a "string". *)
Import Rec Rec_weak.
Open Scope string_scope.
Notation "'!' x" := (_U x _) (at level 9).
(*Notation "{{ }}" := nil_n.*)
Notation "{{ a ; .. ; b }}" := (_R _ (cons_n _ a .. (cons_n _ b nil_n) ..)).
(* *)
Definition _positive := _positive 
  ! "xI" 
  ! "xO" 
  ! "xH".
Definition _Z := _Z _positive 
  ! "Z0" 
  ! "Zpos" 
  ! "Zneg".
Definition _int := _int _Z.
Definition _float := _float _Z.
Definition _ident := _positive.

Definition _init_data := _init_data _int _float _Z _ident
  ! "Init_int8"
  ! "Init_int16"
  ! "Init_int32"
  ! "Init_float32"
  ! "Init_float64"
  ! "Init_space"
  ! "Init_addrof".

Module _AST.
  Definition _program {B C} f_b f_c := @_AST._program _ B C ! "pair" ! "nil" ! "cons" f_b f_c _ident _init_data
    {{ "prog_funct" ; "prog_main" ; "prog_vars" }}.
End _AST.

Definition _signedness := _signedness 
  ! "Signed" 
  ! "Unsigned".
Definition _intsize := _intsize 
  ! "I8" 
  ! "I16" 
  ! "I32".
Definition _floatsize := _floatsize 
  ! "F32" 
  ! "F64".
Definition _type_ T (ty : forall A : Type,
       _type_ A (T -> A) 
         (fun ty : Type =>
          (intsize -> A) ->
          (signedness -> A) ->
          (floatsize -> A) -> (Z -> A) -> (ident -> A) -> ty) ) := ty _ _intsize _signedness _floatsize _Z _ident
  ! "Tvoid"
  ! "Tint"
  ! "Tfloat"
  ! "Tpointer"
  ! "Tarray"
  ! "Tfunction"
  ! "Tstruct"
  ! "Tunion"
  ! "Tcomp_ptr"
  ! "Tnil"
  ! "Tcons"
  ! "Fnil"
  ! "Fcons".
Definition _type := _type_ _ (@_type).
Definition _typelist := _type_ _ (@_typelist).
Definition _unary_operation := _unary_operation 
  ! "Onotbool"
  ! "Onotint"
  ! "Oneg".
Definition _binary_operation := _binary_operation
  ! "Oadd"
  ! "Osub"
  ! "Omul"
  ! "Odiv"
  ! "Omod"
  ! "Oand"
  ! "Oor"
  ! "Oxor"
  ! "Oshl"
  ! "Oshr"
  ! "Oeq"
  ! "One"
  ! "Olt"
  ! "Ogt"
  ! "Ole"
  ! "Oge".
Definition _expr := _expr _float _int _type _ident _unary_operation _binary_operation 
  ! "Expr"
  ! "Econst_int"
  ! "Econst_float"
  ! "Evar"
  ! "Ederef"
  ! "Eaddrof"
  ! "Eunop"
  ! "Ebinop"
  ! "Ecast"
  ! "Econdition"
  ! "Eandbool"
  ! "Eorbool"
  ! "Esizeof"
  ! "Efield".
Definition _label := _ident.
Definition _statement := _statement ! "Some" ! "None" ! "nil" ! "cons"    _expr _label _int
  ! "Sskip"
  ! "Sassign"
  ! "Scall"
  ! "Ssequence"
  ! "Sifthenelse"
  ! "Swhile"
  ! "Sdowhile"
  ! "Sfor"
  ! "Sbreak"
  ! "Scontinue"
  ! "Sreturn"
  ! "Sswitch"
  ! "Slabel"
  ! "Sgoto"
  ! "LSdefault"
  ! "LScase".
Definition _function := _function ! "pair" ! "nil" ! "cons" _ident _type _statement
  {{ "fn_return" ; "fn_params" ; "fn_vars" ; "fn_body" }}.
Definition _fundef := _fundef _function _ident _typelist _type
  ! "Internal"
  ! "External".
Definition _program := _AST._program _fundef _type.

End Mo.

Module Moo := Mo Monad_base.
