Require Import 
  (* compcert *)
  Coqlib
  Integers
  Floats
  AST
  Csyntax
  (* *)
  Bvector.

Module Rec.
(** This module gives a destructor for each local type used to build the main type [Csyntax.program].
For each type [t], Coq furnishes us automatically a function named [t_rect]. We use it to write a function [_t] which behaviour is almost similar to [t_rect] except that :
- if [t] is a mutually declared type, assume that [t] belongs to [t1 ... ti ... tn], then we use the 'Scheme' command to obtain a recursor [_ti_rect] which folds inside [t1 ... tn] (not like [ti_rect]). 
As the constructors of [_t1 ... _tn] are the same, we just do only one general construction named [_t_] which will take one of [_t1 ... _tn] as an extra parameter. The type of this parameter has to be manually written by hand because of the used of higher order type (see the function [_ty_]).
- if [t] is a recursive type, the parameter used before the recursive call parameter is thrown, we do not use it. 
- an extra function of conversion is provided in the case we are converting a polymorphic function (see [_option] or [_list] for example). *)

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
    (_prod : forall A B, (A -> _) -> (B -> _) -> prod A B -> _)
    (_list : forall A, (A -> _) -> list A -> _)
    f_f f_v 
    _ident _init_data
    (f_mk : A -> B -> A -> D) 
    (x : _ F V)
    :=
    f_mk
      (_list _ (_prod _ _ _ident f_f) (prog_funct x)) 
      (_ident (prog_main x)) 
      (_list _ (_prod _ _ (_prod _ _ _ident (_list _ _init_data)) f_v) (prog_vars x)).
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
  { C  EXPR LABEL INT OPTION }
  f_some (f_none : OPTION) 
  (_list : forall A, (A -> _) -> list A -> C) (_expr : _ -> EXPR) (_label : _ -> LABEL) (_int : _ -> INT)
  f_skip f_assign f_call f_sequence f_ifthenelse f_while f_dowhile f_for f_break f_continue f_return f_switch f_label f_goto f_default f_case
  :=
  _statement_ (fun _ => P) (fun _ => P0) 
    f_skip
    (fun e1 e2 => f_assign (_expr e1) (_expr e2))
    (fun o e l => f_call (_option _expr f_some f_none o) (_expr e) (_list _ _expr l))
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
  (_prod : forall A B, (A -> _) -> (B -> _) -> prod A B -> PROD)
  (_list : forall A, (A -> _) -> list A -> LIST) (_ident : _ -> IDENT) (_type : _ -> TYPE) (_statement : _ -> STATEMENT)
  (f_mk : _ -> _ -> _ -> _ -> FUNCTION) 
  x
 :=
  f_mk 
    (_type (fn_return x)) 
    (_list _ (_prod _ _ _ident _type) (fn_params x)) 
    (_list _ (_prod _ _ _ident _type) (fn_vars x))
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
(** For each general function inside the module [Rec], we cast its type to a lower one : each polymorphic type is explicitly instanciated with a single polymorphic one. 
This polymorphic information can be thought as an accumulator staying alive during the whole execution, it can be used for example with a monadic construction.
After this change, we generalize each function construction "_ -> _ -> _ -> _ -> _" to a more general one "_ ^^ _ --> _" by using the NaryFunctions library.
This is useful for later because we will not want to abstract manually the "fun _ => _" during the application time. 
Note that we have to give explicitely the arity of each constructor in each type. *)
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
Definition _program {A B C} : _ -> _ -> _ -> _ -> _ -> _ ->
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
Definition _statement {A} : A ** 1 -> A ** 0 -> _ -> _ -> _ -> _ -> 
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
Definition _function {A} : _ -> _ -> _ -> _ -> _ -> 
  A ** 4 ->
  _ := @_function A _ A _ _ _.
Definition _fundef {A} : _ -> _ -> _ -> _ -> 
  A ** 1 ->
  A ** 3 ->
  _ := @_fundef _ _ _ _ _.

End Rec_weak.


Module Vector.
  (* Convert a [vector] into a [list] with an extra property on its length. *)
  Definition to_list : forall A n, vector A n -> { l : list A | n = List.length l }.
    induction n ; intros.
    exists List.nil.
    trivial.
    inversion X.
    destruct (IHn X0).
    exists (a :: x).
    simpl.
    auto.
  Defined.

  Definition init : forall {A} n, (nat -> A) -> vector A n.
    intros.   
    induction n.
    apply Vnil.
    apply Vcons. apply X.
    trivial.
    trivial.
  Defined.

  Definition map : forall {A B} (f : A -> B) n (v : vector A n), vector B n.
    induction n.
    intros. apply Vnil.
    intros. inversion v.
    apply Vcons. apply f.
    trivial.
    tauto.
  Defined.
End Vector.


Module Type CONSTRUCTOR.
  Require Import NaryFunctions String.

  Parameter t : Type -> Type.
  Parameter v : Type.
  Definition u := (bool * t v) % type.

  Parameter push : string -> t v.

  Parameter save_pos : t v. (* save the current column number in a stack, by looking where is the previous newline *)
  Parameter delete_pos : t v. (* pop the stack *)
  Parameter indent : t v. (* insert a newline and go to the current number in the head of the stack *)
  Parameter indent_depth : t v. (* same as [indent] but insert extra white space depending on the depth we are in the AST *)

  Parameter perform : list (t v) -> t v.
  Parameter ret : forall A, A -> t A.
  Parameter tt : v.

  Parameter _U : 
    bool (* true : the whole need to be protected by a parenthesis. Note that this information is simple hint, the constructor which call [_U] can decide not to do so. *) -> 
    t v (* prefix *) -> 
    t v (* suffix *) -> 
    forall n, 
    vector (t v) n -> (* separator *)
    vector (bool (* true : follow the same choice as the parenthesis hint (indicated by the element we are folding), false : explicit disable the parenthesis (do not consider the hint) *) * (t v (* prefix *) * t v (* suffix *))) (S n) -> (* surrounding *)
    t u ^^ (S n) --> t u.
    (** Generic description of a printing of an uplet constructor *)
    (** Note that some parameters can be merged (like separator and surrounding) but this writting style expansion is rather general *)

  Parameter _positive : positive -> t u.
  Parameter _Z : Z -> t u.
  Parameter _float : float -> t u.
  Parameter _int : int -> t u.
  Parameter _prod : forall A B, (A -> t u) -> (B -> t u) -> prod A B -> t u.
  Parameter _list : forall A, (A -> t u) -> list A -> t u.
End CONSTRUCTOR.


Module Constructor (C : CONSTRUCTOR). 
(** The pretty-printing is done inside this module : for each type, we explicitly write the name of the corresponding constructor inside a "string". *)
Import Rec Rec_weak C.

Require Import NaryFunctions.
Require Import String.
Open Scope string_scope.

Notation "[| a ; .. ; b |]" := (Vcons _ a _ .. (Vcons _ b _ (Vnil _)) ..).
Notation "[ ]" := nil.
Notation "[ a ; .. ; b ]" := (a :: .. (b :: []) ..).
Notation "'\n'" := indent.

Section pr. (** Additional constructors (same as [_U]) is defined here *)

Definition ret {A} := ret A.

Definition eq_zero n :=
  match n with 
    | 0%nat => true
    | _ => false
  end.
  
Definition not_b (b : bool) := if b then false else true.

Definition surr_empty n := Vector.init n (fun _ => (true, (ret tt, ret tt))).

Definition _U_constr : string (* name of the constructor *) -> forall n, t u ^^ n --> t u.
  intros s n.
  case_eq n ; intros.
  apply ncurry.
  intros. exact (ret (false, push s)). 

  clear n H ; rename n0 into n.
  apply (_U true (push (s ++ " ")) (ret tt)).
  induction n.
  exact (Vnil _).
  apply Vcons. exact (push " "). trivial.
  apply surr_empty.
Defined.

Definition _U_infix2 : t v -> t u ^^ 2 --> t u.
  intros s ; refine (_U true (ret tt) (ret tt) _ [| s |] _).
  apply surr_empty.
Defined.

Definition _U_infix3 : t v -> t v -> t u ^^ 3 --> t u.
  intros s1 s2 ; refine (_U true (ret tt) (ret tt) _ [| s1 ; s2 |] _).
  apply surr_empty.
Defined.

Definition _R : forall n, vector string n -> t u ^^ n --> t u.
  intros n l.
  case_eq n ; intros.
  apply ncurry.
  intros. exact (ret (false, push "{||}")).

  apply (_U false (perform [ save_pos ; push "{| "] ) (perform [ push " |}" ; delete_pos ]) ).
  apply Vector.init. exact (fun _ => perform [ \n ; push " ; " ]).
  subst n.
  refine (Vector.map _ _ l) ; clear.
  intros x.
  exact (false, (push (x ++ " := "), ret tt)).
Defined.

Definition _U2 : string -> forall n, vector (option (string * string)) (S n) -> t u ^^ (S n) --> t u.
  intros s n l.
  apply (_U (not_b (eq_zero n)) (push (s ++ " ")) (ret tt) _ (Vector.init _ (fun _ => push " "))).
  refine (Vector.map _ _ l) ; intros.
  refine (true, _).  
  case_eq H ; intros.
  exact (let (p1, p2) := p in (push p1, push p2)).
  exact (ret tt, ret tt).
Defined.

End pr.

Notation "{{ a ; .. ; b }}" := (_R _ (Vcons _ a _ .. (Vcons _ b _ (Vnil _)) ..)).
Notation "'!' x" := (_U_constr x _) (at level 9).
Notation "| x · y" := (_U2 x _ y) (at level 9).

Definition some : t u ^^ 1 --> t u := ! "Some".
Definition none : t u ^^ 0 --> t u := ! "None".

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
  Definition _program {B C} f_b f_c := @_AST._program _ B C _prod _list f_b f_c _ident _init_data
    {{ "prog_funct" ; "prog_main" ; "prog_vars" }}.
End _AST.

Definition _signedness := _signedness 
  ! (*"Signed"*) "++" 
  ! (*"Unsigned"*) "--".
Definition _intsize := _intsize 
  ! (*"I8"*) "_8"
  ! (*"I16"*) "_16" 
  ! (*"I32"*) "_32" .
Definition _floatsize := _floatsize 
  ! (*"F32"*) "_32_" 
  ! (*"F64"*) "_64_" .
Definition _type_ T (ty : forall A : Type,
       _type_ A (T -> A) 
         (fun ty : Type =>
          (intsize -> A) ->
          (signedness -> A) ->
          (floatsize -> A) -> (Z -> A) -> (ident -> A) -> ty) ) := ty _ _intsize _signedness _floatsize _Z _ident
  ! (*"Tvoid"*) "_void"
  ! (*"Tint"*) "_int"
  ! (*"Tfloat"*) "_float"
  ! (*"Tpointer"*) "`*`"
  ! "Tarray"
  | (*! "Tfunction"*) "Λ" · [| Some ("", "") ; None |]
  ! "Tstruct"
  ! "Tunion"
  ! "Tcomp_ptr"
  ! (*"Tnil"*)  "··"
  (*! "Tcons"*) (_U_infix2 (push " ~> "))
  ! (*"Fnil"*) "-·"
  (*! "Fcons"*) (_U_infix3 (push "-") (push " -~> ")).
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
Definition _statement := _statement some none _list _expr _label _int
  ! "Sskip"
  ! "Sassign"
  ! "Scall"
  (*! "Ssequence"*) (_U_infix2 (perform [ indent_depth ; push ">> " ]))
  (*! "Sifthenelse"*) (_U true (perform [ save_pos ; push "If " ]) delete_pos _ [| perform [ push " then" ; \n ; push "  " ] ; perform [ \n ; push "else" ; \n ; push "  " ] |] (surr_empty _))
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
Definition _function := _function _prod _list _ident _type _statement
  {{ "fn_return" ; "fn_params" ; "fn_vars" ; "fn_body" }}.
Definition _fundef := _fundef _function _ident _typelist _type
  ! "Internal"
  | (*! "External"*) "External" · [| None ; Some ("", "") ; None |].
Definition _program := _AST._program _fundef _type.

End Constructor.





Module Monad_list.

Require Import NaryFunctions String.
Open Scope string_scope.

Notation "[ ]" := nil.
Notation "[ a ; .. ; b ]" := (a :: .. (b :: []) ..).
Notation "{{ a ; .. ; b }}" := (Vcons _ a _ .. (Vcons _ b _ (Vnil _)) ..).

Record st := mk_st
  { buf : list string
  ; pos : list nat
  ; depth : nat }.

Inductive state {A} :=
  L (_ : A) (_ : st).

Definition t A := st -> @state A.
Definition u := (bool * t unit) % type.
Definition v := unit.
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

Definition push s : t unit := 
  fun st =>
  ret tt (mk_st (s :: buf st) (pos st) (depth st)).

Definition add_depth : t unit :=
  fun st => 
  ret tt (mk_st (buf st) (pos st) (S (depth st))).

Definition remove_depth : t unit :=
  fun st =>
  ret tt (mk_st (buf st) (pos st) (match depth st with 0 => 0 | S n => n end % nat)). 

Module String.
Definition rev := 
  (fix aux acc s := 
  match s with
    | String a s => aux (String a acc) s
    | _ => acc
  end) EmptyString.

Definition make (n : nat) (c : Ascii.ascii) :=
  (fix aux n :=
  match n with
  | 0 => EmptyString
  | S n => String c (aux n)
  end %nat) n.
End String.

Notation "'\n' x" := (String "010" x) (at level 9).

Definition save_pos : t unit :=
  fun st =>
  let buf_st := buf st in
  
  ret tt (mk_st buf_st ((fix aux l (pos : nat) :=
    match l with
      | [] => pos
      | x :: xs => 
        match index 0 \n"" (String.rev x) with
        | Some n => (pos + n)%nat
        | None => aux xs (pos + length x)%nat
        end
    end) buf_st 0%nat :: pos st) (depth st)).

Require Import Ascii.

Definition indent : t unit :=
  fun st =>
  push (\n (String.make (match pos st with
  | [] => 0
  | x :: _ => x
  end) " " % char)) st.

Definition indent_depth : t unit :=
  fun st =>
  push (\n (String.make (2 * depth st + match pos st with
  | [] => 0
  | x :: _ => x
  end) " " % char)) st.

Definition delete_pos : t unit :=
  fun st =>
  ret tt (mk_st (buf st) (List.tail (pos st)) (depth st)).

Definition and_b (b1 b2 : bool) : bool.
  intros.
  case_eq b1 ; case_eq b2 ; intros.
  exact true. exact false. exact false. exact false.
Defined.

Definition eval (a : (bool * (t v * t v)) * _) := 
  let (a, m) := a in
  let (bb, m1_m2) := a in let (m1, m2) := m1_m2 in
  perform 
  [ m1
  ; bind m (fun (b_m : bool * t unit) => let (b, m) := b_m in if and_b bb b then perform [ push "(" ; m ; push ")" ] else m)
  ; m2 ].

Definition _U_aux : forall
  (b : bool)
  (pref : t v)
  (suff : t v)
  (n : nat)
  (sep : vector (t v) n)
  (surr : vector (bool * (t v * t v)) (S n))
  (l : list (t u))
  (_ : l <> nil),
  t u.
  intros.
  case_eq l. tauto.
  intros x xs _.
  refine (ret (b, _)) ; clear b.
  (* (* put this below to display the depth as a Coq comment *)  
    fun st => push ("(*" ++ (String (ascii_of_nat (depth st + 48)) EmptyString) ++ "*)") st ;     *)
  refine (perform [ add_depth ; pref ; _ ; suff ; remove_depth ]) ; clear pref suff.
  inversion surr ; clear surr ; rename X into surr.
  refine (_ (eval (a, x))) ; clear a x n0 H1.
  pose (v_to_list A v := let (l, _) := Vector.to_list A n v in l).
  refine (List.fold_left _ (List.combine (v_to_list _ sep) (List.combine (v_to_list _ surr) xs) )) ; clear sep surr xs.
  intros acc (sep, a).
  exact (perform [ acc ; sep ; eval a ]).
Defined.

Definition _U : 
    bool -> 
    t v -> 
    t v -> 
    forall n, 
    vector (t v) n -> 
    vector (bool * (t v * t v)) (S n) -> 
    t u ^^ (S n) --> t u. 
  intros b pref suff n sep surr.
  apply ncurry.
  intro cpl.
  apply (_U_aux b pref suff n sep surr (nprod_to_list _ _ cpl)).
  destruct cpl.
  simpl.
  auto with *.
Defined.

(*
Module Expand.
Notation "'!' x" := (_U_constr x _) (at level 9).

Definition _positive := Rec_weak._positive 
  ! "xI" 
  ! "xO" 
  ! "xH".

Definition _Z := Rec_weak._Z _positive 
  ! "Z0"
  ! "Zpos" 
  ! "Zneg".
End Expand.
*)

Module Simpl.
Require Import Euclid.
Require Import Recdef.

Definition ascii_to_string a := String a "".
Coercion ascii_to_string : ascii >-> string.
Definition ascii_of_number n := ascii_of_nat (n + 48).
Coercion ascii_of_number : nat >-> ascii.

Open Scope nat_scope.

Remark gt_10_0 : 10 > 0.
  omega.
Qed.

Function string_of_nat_aux (acc : string) (n : nat) {wf lt n} : string := 
  match n with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 => n ++ acc
  | _ => 
    let (q, pr_q) := quotient 10 gt_10_0 n in
    let (r, _) := modulo 10 gt_10_0 n in 
      string_of_nat_aux (r ++ acc)
      q
  end.
  intros.
  inversion pr_q.
  omega.
  auto with *.
Defined.

(* (* WARNING This proof is not accepted by Coq 8.2, but 8.3 is ok. *)
Function string_of_nat_aux (acc : string) (n : nat) {wf lt n} : string := 
  match n with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 => n ++ acc
  | _ => 
    string_of_nat_aux 
      (let (r, _) := modulo 10 gt_10_0 n in r ++ acc) 
      (let (q, _) := quotient 10 gt_10_0 n in q)
  end.
  intros.
  match goal with |- context [ ?Q ?a ?b ?c ] => destruct (Q a b c) as (q, pr_q) end.
  inversion pr_q.
  omega.
  auto with *.
Qed.
*)

Definition string_of_nat_ := string_of_nat_aux "".

Definition string_of_positive_ p :=
  string_of_nat_ (nat_of_P p).

Definition string_of_positive p := "`" ++ string_of_positive_ p.

Definition string_of_Z z := 
  match z with
    | Z0 => "0"
    | Zpos p => string_of_positive_ p
    | Zneg p => "-" ++ string_of_positive_ p
  end.

Definition _positive p := push (string_of_positive p).
Definition _Z z := push (string_of_Z z).
End Simpl.

Definition _positive p := ret (false, Simpl._positive p).
Definition _Z z := ret (false, Simpl._Z z).

Definition number f_conv (m : t u) := ret (false, perform
  [ push f_conv
  ; bind m (fun b_m => let (_, m) := b_m in m) ]).

Definition _int i := number "``" (_Z (Int.intval i)).
Definition _float f := number "·" (_int (Float.intoffloat f)).

Definition _prod : forall A B, (A -> t u) -> (B -> t u) -> prod A B -> t u.
  intros A B fa fb (a, b).
  eapply (_U_aux false (push "(") (push ")") _ {{ push ", " }} (Vector.init _ (fun _ => (false, (ret tt, ret tt)))) [ fa a ; fb b ]).
  auto with *.
Defined.

Definition _list : forall A, (A -> t u) -> list A -> t u.
  intros A f l.
  case_eq l ; intros.
  exact (ret (false, push "[]")).
  apply (_U_aux false (perform [ save_pos ; push "[ " ]) (perform [ push " ]" ; delete_pos ]) (List.length l) (Vector.init _ (fun _ => perform [ indent ; push "; " ] )) 
    (Vector.init _ (fun _ => (false, (ret tt, ret tt)))) (List.map f l)).
  rewrite H. simpl.
  auto with *.
Defined.

Definition tt := tt.

End Monad_list.



(** Main function *)
Module Constructor_list := Constructor Monad_list.
Require Import String.
Import Monad_list.

Definition program_fundef_type ast := 
  match bind (Constructor_list._program ast)
    (fun b_m => let (_, m) := b_m in m) (mk_st nil [] 0)
  with
    L _ st => List.app 
      (List.map (fun s => s ++ \n"")
      [ "Require Import" 
      ; "  (* compcert *)"
      ; "  Coqlib"
      ; "  Integers"
      ; "  Floats"
      ; "  AST"
      ; "  Csyntax"
      ; "  ."
      ; ""
      ; "Notation ""` x"" := (x % positive) (at level 9)."
      ; "Notation ""`` x"" := (Int.repr x) (at level 9)."
      ; "Notation ""· x"" := (Float.floatofint x) (at level 9)."
      ; "Notation ""[ ]"" := nil."
      ; "Notation ""[ a ; .. ; b ]"" := (a :: .. (b :: []) ..)."
      ; "Notation ""a ~> b"" := (Tcons a b) (at level 9, right associativity)."
      ; "Notation ""··"" := Tnil."
      ; "Notation ""-·"" := Fnil."
      ; "Notation ""`*`"" := Tpointer."
      ; "Notation ""a - b -~> c"" := (Fcons a b c) (at level 9, right associativity)."
      ; "Notation ""a >> b"" := (Ssequence a b) (at level 9)."
      ; "Notation ""++"" := Signed."
      ; "Notation ""--"" := Unsigned."
      ; "Notation _8 := I8."
      ; "Notation _16 := I16."
      ; "Notation _32 := I32."
      ; "Notation _32_ := F32."
      ; "Notation _64_ := F64."
      ; "Notation _int := Tint."
      ; "Notation _float := Tfloat."
      ; "Notation _void := Tvoid."
      ; "Notation ""'Λ'"" := Tfunction."
      ; "Notation ""'If' a 'then' b 'else' c"" := (Sifthenelse a b c) (at level 9)."
      ; ""

      ; "Definition a :=" ])
      (List.rev ((\n"." ++ \n"Print a.") :: buf st))
  end
.
