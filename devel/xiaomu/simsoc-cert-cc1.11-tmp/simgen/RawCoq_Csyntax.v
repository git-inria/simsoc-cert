(**
SimSoC-Cert, a toolkit for generating certified processor simulators
See the COPYRIGHTS and LICENSE files.

Pretty-printer for CompCert type [AST.program fundef type].
*)

Require Import 
  (* compcert *)
  Coqlib
  Integers
  Floats
  Values
  AST
  Csyntax
  Ordered
  (* stdlib *)
  Bvector
  NaryFunctions
  FMapAVL.

  Close Scope vector_scope.

(****************************************************************************)
(** Utilitaries *)

Module Vector.

  (* Convert a [vector] into a [list] with an extra property on its length. *)

  (* For Coq-8.3pl4 and older version: *)
  (*
  Definition to_list : forall A n,
    vector A n -> { l : list A | n = List.length l }.

  Proof.
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

  Proof.
    intros.   
    induction n.
    apply Vnil.
    apply Vcons. apply X.
    trivial.
    trivial.
  Defined.

  Definition map : forall {A B} (f : A -> B) n (v : vector A n), vector B n.

  Proof.
    induction n.
    intros. apply Vnil.
    intros. inversion v.
    apply Vcons. apply f.
    trivial.
    tauto.
  Defined.
*)

(* For Coq-8.4: *)

  Definition to_list : forall A n,
    Vector.t A n -> { l : list A | n = List.length l }.

  Proof.
    induction n ; intros.
    exists List.nil.
    trivial.
    inversion X.
    destruct (IHn X0).
    exists (h :: x).
    simpl.
    auto.
  Defined.

  Definition init : forall {A} n, (nat -> A) -> Vector.t A n.

  Proof.
    intros.   
    induction n.
    apply Vector.nil.
    apply Vector.cons. apply X.
    trivial.
    trivial.
  Defined.

  Definition map : forall {A B} (f : A -> B) n (v : Vector.t A n), Vector.t B n.

  Proof.
    induction n.
    intros. apply Vector.nil.
    intros. inversion v.
    apply Vector.cons. apply f.
    trivial.
    tauto.
  Defined.

End Vector.

(****************************************************************************)
(** Generic creation of a recursor

This module gives a destructor for each local type used to build the
main type [Csyntax.program]. For each type [t], Coq furnishes us
automatically a function named [t_rect]. We use it to write a function
[_t] which behaviour is almost similar to [t_rect] except that :

- if [t] is a mutually declared type, assume that [t] belongs to [t1
  ... ti ... tn], then we use the 'Scheme' command to obtain a
  recursor [_ti_rect] which folds inside [t1 ... tn] (not like
  [ti_rect]).

As the constructors of [_t1 ... _tn] are the same, we just do only one
general construction named [_t_] which will take one of [_t1 ... _tn]
as an extra parameter. The type of this parameter has to be manually
written by hand because of the used of higher order type (see the
function [_ty_]).

- if [t] is a recursive type, the parameter used before the recursive
  call parameter is thrown, we do not use it.

- an extra function of conversion is provided in the case we are
  converting a polymorphic function (see [_option] or [_list] for
  example). *)

Module Rec.

  Definition _option {A B C} (a : _ -> C) f :=
    @option_rect A (fun _ => B) (fun x => f (a x)).

  Definition _positive {A} f f0 :=
    @positive_rect (fun _ => A) (fun _ x => f x) (fun _ x => f0 x).

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

    Definition _globvar {A B C E INIT_DATA V : Type}
      (_list : forall A, (A -> _) -> list A -> _)
      _bool
      f_v
      (_init_data : _ -> INIT_DATA)
      (f_mk : A -> B -> C -> C -> E) 
      (x : _ V)
      :=
      f_mk
      (f_v (gvar_info x))
      (_list _ _init_data (gvar_init x))
      (_bool (gvar_readonly x))
      (_bool (gvar_volatile x)).

    Definition _program {A B C D E INIT_DATA GLOBVAR F V : Type}
      (_prod : forall A B, (A -> _) -> (B -> _) ->  A * B -> C)
      (_list : forall A, (A -> _) -> list A -> _)
      f_f (f_v : V -> E) 
      _ident (_init_data : init_data -> INIT_DATA)
      (_globvar : _ -> _ -> GLOBVAR)
      (f_mk : A -> B -> A -> D) 
      (x : _ F V)
      :=
      f_mk
      (_list _ (_prod _ _ _ident f_f) (prog_funct x)) 
      (_ident (prog_main x)) 
      (_list _ (_prod _ _ _ident (_globvar f_v)) (prog_vars x)).

    Definition _program2 {A B C D E INIT_DATA GLOBVAR F V : Type}
      (_prod : forall A B, (A -> _) -> (B -> _) -> prod A B -> C)
      (_list : forall A, (A -> _) -> list A -> _)
      (_list2 : forall A, (A -> _) -> list A -> _)
      f_f (f_v : V -> E) 
      _ident (_init_data : init_data -> INIT_DATA)
      (_globvar : _ -> _ -> GLOBVAR)
      (f_mk : A -> B -> A -> D) 
      (x : _ F V)
      :=
      f_mk
      (_list _ (_prod _ _ _ident f_f) (prog_funct x)) 
      (_ident (prog_main x)) 
      (_list2 _ (_prod _ _ _ident (_globvar f_v)) (prog_vars x)).

    Definition _typ {A} := typ_rect (fun _ => A).

    Definition _signature {A B C TYP}
      (_list : forall A, (A -> _) -> list A -> _)
      (_option : forall A, (A -> _) -> option A -> _)
      (_typ : _ -> TYP)
      (f_mk : A -> B -> C)
      x
      :=
      f_mk
      (_list _ _typ (sig_args x))
      (_option _ _typ (sig_res x)).

    Definition _memory_chunk {A}
      :=
      memory_chunk_rect (fun _ => A).


    (* Changed from CompCert-1.9 to CompCert-1.11, inductive type 
       "external_function_rect" has two more constructor "EF_vload_global" and
       "EF_vstore global". See AST.v *)
    Definition _external_function {A IDENT MEMORY_CHUNK SIGNATURE Z INT TYP}
      (_list : forall A, (A -> _) -> list A -> _)
      (_ident : _ -> IDENT)
      (_memory_chunk : _ -> MEMORY_CHUNK)
      (_signature : _ -> SIGNATURE)
      (_Z : _ -> Z)
      (_INT : _ -> INT)
      (_typ : _ -> TYP)
      f_external f_builtin f_vload f_vstore f_vload_global f_vstore_global f_malloc f_free f_memcpy (f_annot : _ -> A -> _) f_annot_val
      := 
      external_function_rect (fun _ => A)
        (fun n s => f_external (_ident n) (_signature s))
        (fun n s => f_builtin (_ident n) (_signature s))
        (fun c => f_vload (_memory_chunk c))
        (fun c => f_vstore (_memory_chunk c))
        (fun c n ofs => f_vload_global (_memory_chunk c) (_ident n) (_INT ofs))
        (fun c n ofs => f_vstore_global (_memory_chunk c) (_ident n) (_INT ofs))
        f_malloc
        f_free
        (fun sz al => f_memcpy (_Z sz) (_Z al))
        (fun i l => f_annot (_ident i) (_list _ _typ l))
        (fun i t => f_annot_val (_ident i) (_typ t)).

  End _AST.

  Module _Values.

    Definition _val {A INT FLOAT BLOCK} 
      (_int : _ -> INT) (_float : _ -> FLOAT) (_block : _ -> BLOCK)
      f_undef f_int f_float f_ptr
      :=
      val_rect (fun _ => A)
      f_undef
      (fun i => f_int (_int i))
      (fun f => f_float (_float f))
      (fun p i => f_ptr (_block p) (_int i)).

  End _Values.

  Definition _signedness {A} := signedness_rect (fun _ => A).
  Definition _intsize {A} := intsize_rect (fun _ => A).
  Definition _floatsize {A} := floatsize_rect (fun _ => A).
  (* Changed from CompCert-1.9 to CompCert-1.11, add Record type "attr".
     See Csyntax.v *)
  Definition _attr {A B}
    _bool
    (f_mk : A -> B)
    x
    :=
    f_mk
    (_bool (attr_volatile x)).

  Scheme _type_rect := Induction for type Sort Type
  with _typelist_rect := Induction for typelist Sort Type
  with _fieldlist_rect := Induction for fieldlist Sort Type.

  (* Changed from CompCert-1.9 to CompCert-1.11, inductive type "type" has been
     added a set of attributes "attr". See Csyntax.v *)
  Definition _ty_ AA P P0 P1 
    (f_ty : forall (P : type -> Type) (P0 : typelist -> Type)
      (P1 : fieldlist -> Type),
      P Tvoid ->
      (forall (i : intsize) (s : signedness) (a : attr), P (Tint i s a)) ->
      (forall (f1 : floatsize) (a : attr), P (Tfloat f1 a)) ->
      (forall (t : type), P t -> forall a, P (Tpointer t a)) ->
      (forall (t : type), P t -> forall (z : Z) (a : attr), P (Tarray t z a)) ->
      (forall t : typelist,
        P0 t -> forall t0 : type, P t0 -> P (Tfunction t t0)) ->
      (forall (i : ident) (f5 : fieldlist), P1 f5 -> forall a, P (Tstruct i f5 a)) ->
      (forall (i : ident) (f6 : fieldlist), P1 f6 -> forall a, P (Tunion i f6 a)) ->
      (forall (i : ident) (a : attr), P (Tcomp_ptr i a)) ->
      P0 Tnil ->
      (forall t : type,
        P t -> forall t0 : typelist, P0 t0 -> P0 (Tcons t t0)) ->
      P1 Fnil ->
      (forall (i : ident) (t : type),
        P t -> forall f11 : fieldlist, P1 f11 -> P1 (Fcons i t f11)) ->
      AA P P0 P1)
    {A B C D E F}
    (_intsize : _ -> A) (_signedness : _ -> B) (_floatsize : _ -> C)
    (_Z : _ -> D) (_ident : _ -> E) (_attr : _ -> F)
    f_void f_int f_float f_pointer f_array f_function f_struct f_union
    f_comp_ptr f_tnil f_tcons f_fnil f_fcons
    := f_ty (fun _ => P) (fun _ => P0) (fun _ => P1)
    f_void
    (fun i s a => f_int (_intsize i) (_signedness s) (_attr a))
    (fun f a => f_float (_floatsize f) (_attr a))
    (fun _ aux a => f_pointer aux (_attr a))
    (fun _ aux z a => f_array aux (_Z z) (_attr a))
    (fun _ aux0 _ aux1 => f_function aux0 aux1)
    (fun i _ aux a => f_struct (_ident i) aux (_attr a))
    (fun i _ aux a => f_union (_ident i) aux (_attr a))
    (fun i a => f_comp_ptr (_ident i) (_attr a))
    f_tnil
    (fun _ aux1 _ aux2 => f_tcons aux1 aux2)
    f_fnil
    (fun i _ aux1 _ aux2 => f_fcons (_ident i) aux1 aux2).

  Definition _type {P P0 P1} := @_ty_ _ P P0 P1 _type_rect.
  Definition _typelist {P P0 P1} := @_ty_ _ P P0 P1 _typelist_rect.
  Definition _fieldlist {P P0 P1} := @_ty_ _ P P0 P1 _fieldlist_rect.

  Definition _unary_operation {A} := unary_operation_rect (fun _ => A).
  Definition _binary_operation {A} := binary_operation_rect (fun _ => A).
  Definition _incr_or_decr {A} := incr_or_decr_rect (fun _ => A).

  Scheme _expr_rect := Induction for expr Sort Type
  with _exprlist_rect := Induction for exprlist Sort Type.

  (* Changed from CompCert-1.9 to CompCert-1.11, inductive type has been added
     one constructor "Ealignof". See Csyntax.v *)
  Definition _expr_ A P P0
    (_expr_ : forall (P : expr -> Type) (P0 : exprlist -> Type),
      (forall (v : Values.val) (ty : type), P (Eval v ty)) ->
      (forall (x : ident) (ty : type), P (Evar x ty)) ->
      (forall l : expr,
        P l -> forall (f1 : ident) (ty : type), P (Efield l f1 ty)) ->
      (forall l : expr, P l -> forall ty : type, P (Evalof l ty)) ->
      (forall r : expr, P r -> forall ty : type, P (Ederef r ty)) ->
      (forall l : expr, P l -> forall ty : type, P (Eaddrof l ty)) ->
      (forall (op : unary_operation) (r : expr),
        P r -> forall ty : type, P (Eunop op r ty)) ->
      (forall (op : binary_operation) (r1 : expr),
        P r1 ->
        forall r2 : expr, P r2 -> forall ty : type, P (Ebinop op r1 r2 ty)) ->
      (forall r : expr, P r -> forall ty : type, P (Ecast r ty)) ->
      (forall r1 : expr,
        P r1 ->
        forall r2 : expr,
          P r2 ->
          forall r3 : expr,
            P r3 -> forall ty : type, P (Econdition r1 r2 r3 ty)) ->
      (forall ty' ty : type, P (Esizeof ty' ty)) ->
      (forall ty' ty : type, P (Ealignof ty' ty)) ->
      (forall l : expr,
        P l -> forall r : expr, P r -> forall ty : type, P (Eassign l r ty)) ->
      (forall (op : binary_operation) (l : expr),
        P l ->
        forall r : expr,
          P r -> forall tyres ty : type, P (Eassignop op l r tyres ty)) ->
      (forall (id : incr_or_decr) (l : expr),
        P l -> forall ty : type, P (Epostincr id l ty)) ->
      (forall r1 : expr,
        P r1 ->
        forall r2 : expr, P r2 -> forall ty : type, P (Ecomma r1 r2 ty)) ->
      (forall r1 : expr,
        P r1 ->
        forall rargs : exprlist,
          P0 rargs -> forall ty : type, P (Ecall r1 rargs ty)) ->
      (forall (b : Values.block) (ofs : int) (ty : type), P (Eloc b ofs ty)) ->
      (forall r : expr, P r -> forall ty : type, P (Eparen r ty)) ->
      P0 Enil ->
      (forall r1 : expr,
        P r1 -> forall rl : exprlist, P0 rl -> P0 (Econs r1 rl)) ->
      A P P0)
    {VAL INT TYPE IDENT UNARY_OPERATION BINARY_OPERATION BLOCK INCR_OR_DECR}
    (_val : _ -> VAL) (_int : _ -> INT) (_type : _ -> TYPE)
    (_ident : _ -> IDENT) (_unary_operation : _ -> UNARY_OPERATION)
    (_binary_operation : _ -> BINARY_OPERATION) (_block : _ -> BLOCK)
    (_incr_or_decr : _ -> INCR_OR_DECR)
    f_val f_var f_field f_valof f_deref f_addrof f_unop f_binop f_cast
    f_condition f_sizeof f_alignof f_assign f_assignop f_postincr f_comma f_call
    f_loc f_paren f_nil f_cons 
    := 
    _expr_ (fun _ => P) (fun _ => P0)
    (fun v ty => f_val (_val v) (_type ty))
    (fun i ty => f_var (_ident i) (_type ty))
    (fun _ aux i ty => f_field aux (_ident i) (_type ty))
    (fun _ aux ty => f_valof aux (_type ty))
    (fun _ aux ty => f_deref aux (_type ty))
    (fun _ aux ty => f_addrof aux (_type ty))
    (fun u _ aux ty => f_unop (_unary_operation u) aux (_type ty))
    (fun b _ aux1 _ aux2 ty =>
      f_binop (_binary_operation b) aux1 aux2 (_type ty))
    (fun _ aux ty => f_cast aux (_type ty))
    (fun _ aux1 _ aux2 _ aux3 ty => f_condition aux1 aux2 aux3 (_type ty))
    (fun t ty => f_sizeof (_type t) (_type ty))
    (fun t ty => f_alignof (_type t) (_type ty))
    (fun _ aux1 _ aux2 ty => f_assign aux1 aux2 (_type ty))
    (fun b _ aux2 _ aux3 ty1 ty2 =>
      f_assignop (_binary_operation b) aux2 aux3 (_type ty1) (_type ty2))
    (fun i _ aux1 ty => f_postincr (_incr_or_decr i) aux1 (_type ty))
    (fun _ aux1 _ aux2 ty => f_comma aux1 aux2 (_type ty))
    (fun _ aux1 _ aux2 ty => f_call aux1 aux2 (_type ty))
    (fun b i ty => f_loc (_block b) (_int i) (_type ty))
    (fun _ aux1 ty => f_paren aux1 (_type ty))
    f_nil
    (fun _ aux1 _ aux2 => f_cons aux1 aux2).

  Definition _expr {P P0} := @_expr_ _ P P0 _expr_rect.
  Definition _exprlist {P P0} := @_expr_ _ P P0 _exprlist_rect.

  Scheme _statement_rect := Induction for statement Sort Type
  with _labeled_statements_rect := Induction for labeled_statements Sort Type.

  Definition _statement_ A P P0 
    (_statement_ : forall (P : statement -> Type)
      (P0 : labeled_statements -> Type),
      P Sskip ->
      (forall e : expr, P (Sdo e)) ->
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
        P s -> forall l : labeled_statements, P0 l -> P0 (LScase i s l)) ->
      A P P0)
    { EXPR LABEL INT OPTION }
    (_option : forall A, (A -> _) -> option A -> OPTION)
    (_expr : _ -> EXPR) (_label : _ -> LABEL) (_int : _ -> INT)
    f_skip f_do f_sequence f_ifthenelse f_while f_dowhile f_for f_break
    f_continue f_return f_switch f_label f_goto f_default f_case
    :=
    _statement_ (fun _ => P) (fun _ => P0) 
    f_skip
    (fun e => f_do (_expr e))
    (fun _ aux1 _ aux2 => f_sequence aux1 aux2)
    (fun e _ aux1 _ aux2 => f_ifthenelse (_expr e) aux1 aux2)
    (fun e _ aux => f_while (_expr e) aux)
    (fun e _ aux => f_dowhile (_expr e) aux)
    (fun _ aux1 e _ aux2 _ aux3 => f_for aux1 (_expr e) aux2 aux3)
    f_break
    f_continue
    (fun o => f_return (_option _ _expr o))
    (fun e _ aux => f_switch (_expr e) aux)
    (fun l _ aux => f_label (_label l) aux)
    (fun l => f_goto (_label l))
    (fun _ aux => f_default aux)
    (fun i _ aux1 _ aux2 => f_case (_int i) aux1 aux2).

  Definition _statement {P P0} := @_statement_ _ P P0 _statement_rect.
  Definition _labeled_statements {P P0} :=
    @_statement_ _ P P0 _labeled_statements_rect.

  Definition _function { PROD LIST IDENT TYPE STATEMENT FUNCTION}
    (_prod : forall A B, (A -> _) -> (B -> _) -> prod A B -> PROD)
    (_list : forall A, (A -> _) -> list A -> LIST) (_ident : _ -> IDENT)
    (_type : _ -> TYPE) (_statement : _ -> STATEMENT)
    (f_mk : _ -> _ -> _ -> _ -> FUNCTION) 
    x
    :=
    f_mk 
    (_type (fn_return x)) 
    (_list _ (_prod _ _ _ident _type) (fn_params x)) 
    (_list _ (_prod _ _ _ident _type) (fn_vars x))
    (_statement (fn_body x)).

  Definition _fundef {A  FUNCTION IDENT TYPELIST TYPE}
    (_function : _ -> FUNCTION) (_ident : _ -> IDENT)
    (_typelist : _ -> TYPELIST) (_type : _ -> TYPE)
    f_internal f_external
    :=
    fundef_rect (fun _ => A)
    (fun x => f_internal (_function x))
    (fun i tl t => f_external (_ident i) (_typelist tl) (_type t)).

End Rec.

(****************************************************************************)
(** For each general function inside the module [Rec], we cast its
type to a lower one : each polymorphic type is explicitly instanciated
with a single polymorphic one.  This polymorphic information can be
thought as an accumulator staying alive during the whole execution, it
can be used for example with a monadic construction. After this
change, we generalize each function construction "_ -> _ -> _ -> _ ->
_" to a more general one "_ ^^ _ --> _" by using the NaryFunctions
library. This is useful for later because we do not want to abstract
manually the "fun _ => _" during the application time. Note that we
have to give explicitely the arity of each constructor in each
type. *)

Module Rec_weak.

  Import Rec.

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

    Definition _globvar {A B} : _ -> _ -> _ -> _ ->
      A ** 4 ->
      _ := @_AST._globvar _ _ _ _ A B.

    Definition _program {A B C} : _ -> _ -> _ -> _ -> _ -> _ -> _ ->
      A ** 3 ->
      _ := @_AST._program _ _ A _ A A A B C.

    Definition _typ {A} : 
      A ** 0 ->
      A ** 0 ->
      _ := @_AST._typ A.

    Definition _signature {A} : _ -> _ -> _ ->
      A ** 2 -> 
      _ := @_AST._signature _ _ _ A.

    Definition _memory_chunk {A} : 
      A ** 0 ->
      A ** 0 ->
      A ** 0 ->
      A ** 0 ->
      A ** 0 ->
      A ** 0 ->
      A ** 0 ->
      _ := @_AST._memory_chunk A.

    (* 1.9 -> 1.11 One more parameter "INT". See AST.v *)
    Definition _external_function {A} : _ -> _ -> _ -> _ -> _ -> _ -> _ -> 
      A ** 2 -> 
      A ** 2 -> 
      A ** 1 -> 
      A ** 1 ->
      A ** 3 -> 
      A ** 3 ->
      A ** 0 -> 
      A ** 0 -> 
      A ** 2 -> 
      A ** 2 -> 
      A ** 2 -> 
      _ := @_AST._external_function _ _ _ _ _ _ _.

  End _AST.

  Module _Values.

    Definition _val {A} : _ -> _ -> _ ->
      A ** 0 ->
      A ** 1 ->
      A ** 1 ->
      A ** 2 ->
      _ := @_Values._val _ _ _ _.

  End _Values.

  Definition _signedness {A} :
    A ** 0 ->
    A ** 0 ->
    _ := @_signedness _.

  (* 1.9 -> 1.11 type "intsize" add constructor "IBool". See Csyntax.v *)
  Definition _intsize {A} :
    A ** 0 ->
    A ** 0 ->
    A ** 0 ->
    A ** 0 ->
    _ := @_intsize _.

  Definition _floatsize {A} :
    A ** 0 ->
    A ** 0 ->
    _ := @_floatsize _.

  (* 1.9 -> 1.11 new type attr. See Csyntax.v *)
  Definition _attr {A} : _->
    A ** 1 ->
    _ := @_attr _ A.

  (* 1.9 -> 1.11 number of parameters is changed. See Csyntax.v *)
  Definition _type_ A B (f : _ -> Type) := f (
    A ** 0 ->
    A ** 3 ->
    A ** 2 ->
    A ** 2 ->
    A ** 3 ->
    A ** 2 ->
    A ** 3 ->
    A ** 3 ->
    A ** 2 ->
    A ** 0 ->
    A ** 2 ->
    A ** 0 ->
    A ** 3 ->
    B).

  (* 1.9 -> 1.11 number of parameters is changed. See Csyntax.v *)
  Definition _type {A} : _type_ A _ (fun ty => _ -> _ -> _ -> _ -> _ -> _ -> ty)
    := @_type _ _ _ _ _ _ _ _ _.

  (* 1.9 -> 1.11 number of parameters is changed. See Csyntax.v *)
  Definition _typelist {A} : _type_ A _ (fun ty => _ -> _ -> _ -> _ -> _ -> _ -> ty)
    := @_typelist _ _ _ _ _ _ _ _ _.

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

  (* 1.9 -> 1.11 number of parameters is changed. See Csyntax.v *)
  Definition _expr {A} : _ -> _ -> _ -> _ -> _ -> _ -> _ -> _ ->
    A ** 2 -> 
    A ** 2 -> 
    A ** 3 -> 
    A ** 2 -> 
    A ** 2 -> 
    A ** 2 -> 
    A ** 3 -> 
    A ** 4 -> 
    A ** 2 -> 
    A ** 4 -> 
    A ** 2 -> 
    A ** 2 -> 
    A ** 3 -> 
    A ** 5 -> 
    A ** 3 -> 
    A ** 3 -> 
    A ** 3 -> 
    A ** 3 -> 
    A ** 2 -> 
    A ** 0 -> 
    A ** 2 -> 
    _ := @_expr _ _ _ _ _ _ _ _ _ _.

  Definition _incr_or_decr {A} : 
    A ** 0 ->
    A ** 0 ->
    _ := @_incr_or_decr _.

  Definition _statement {A} : _ -> _ -> _ -> _ -> 
    A ** 0 -> 
    A ** 1 -> 
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
    _ := @_statement _ _ _ _ _ _.

  Definition _function {A} : _ -> _ -> _ -> _ -> _ -> 
    A ** 4 ->
    _ := @_function A _ A _ _ _.

  Definition _fundef {A} : _ -> _ -> _ -> _ -> 
    A ** 1 ->
    A ** 3 ->
    _ := @_fundef _ _ _ _ _.

End Rec_weak.

(****************************************************************************)
(** For the following module type, the implementation is done at OCaml side *)

Module Type STRING.
  Parameter t : Type.
  Parameter of_string : String.string -> t.
  Parameter make : nat -> Ascii.ascii -> t.
  Parameter append : t -> t -> t.
End STRING.

Module Type UTIL (S : STRING).
  (* we can also implement these [string_of_...] functions in Coq, but
  in the case of not tail recursive function, we may have a
  ([Stack_overflow], in byte code) or a (Segmentation_fault, in native
  code). *)
  Parameter string_of_nat : nat -> S.t.
  Parameter string_of_positive : positive -> S.t.
  Parameter string_of_Z : Z -> S.t.

  (* look at the hashtbl [string_of_atom] inside 'Camlcoq.ml' and
  return the name of the corresponding positive if found.  If found,
  it returns the pair composed of the string name escaped and the
  original name ([None] in the case the original name do not conflict
  with a Coq keyword) *)
  Parameter name : positive -> option (S.t * option S.t).

  Parameter map_stringTable : forall A, list A -> list (A * option S.t).
End UTIL.

Module Type FRESH.
  Parameter t : Type.
  Parameter zero : t.
  Parameter succ : t -> t.
End FRESH.

Module Type BUFFER (S : STRING) (F : FRESH).
  Parameter t : Type.
  Parameter empty : forall A, A -> t.
  Parameter print : S.t -> t -> t.
  Parameter print_newline : t -> t.
  Parameter print_ident : F.t -> t -> t.
  Parameter pos : t -> nat. (* number of character since the last call to [print_newline] or [empty] *)
  Parameter add_buffer : t -> t -> t.
End BUFFER.

Module Type KEY.
  Parameter t : Type.
End KEY.

Module Type MAP (K : KEY). (** using OCaml structural equality *)
  Parameter t : Type -> Type.
  Parameter add : forall A, K.t -> A -> t A -> t A.
  Parameter find : forall A, K.t -> t A -> option A.
  Parameter empty : forall A, t A.
  Parameter fold : forall A B, (K.t -> A -> B -> B) -> t A -> B -> B. 
End MAP.

(****************************************************************************)
(** Organization of the whole program of pretty printing *)

Module Type MONAD_SIMPLE (S : STRING).

  Parameter t : Type -> Type.
  Parameter v : Type. (* contains a buffer *)

  Parameter bind : forall A B : Type, t A -> (A -> t B) -> t B.
  Parameter perform : list (t v) -> t v.
  Parameter ret : forall A, A -> t A.

  Parameter print : S.t -> t v. (* print the string into the monadic buffer *)
  Parameter print_type : type -> t v. (* special handling for type, where an identifier is printed instead of the raw type *)
  Parameter print_typelist : typelist -> t v. (* special handling for typelist, where an identifier is printed instead of the raw type *)

  Parameter save_pos : t v. (* save the current column number in a stack, by looking where is the previous newline *)
  Parameter delete_pos : t v. (* pop the stack *)
  Parameter indent : t v. (* insert a newline and go to the current number in the head of the stack *)

  Parameter add_depth : t v. (* this function is used to increment the depth of the current constructor we are crossing *)
  Parameter remove_depth : t v. (* reverse of [add_depth] *)
  Parameter indent_depth : t v. (* same as [indent] but also insert extra white space depending on the depth we are in the AST *)

  Parameter add_used_var : positive -> S.t * option S.t -> t v. (* update the monadic map with the information describing the association of (position, name) *)

  Parameter tt : v.

End MONAD_SIMPLE.

(****************************************************************************)
(** This module type permits the choice between explicit parenthesis
and parenthesis by need *)

Module Type PARENTHESIS (S : STRING) (M : MONAD_SIMPLE S).
  Import M.

  Parameter u : Type. (* depending on the parenthesis mode, [u] is
  equal to [v] or contains a not evaluated [t v] *)

  Parameter ret_u : bool (* hint signaling that the expression [t v]
  need to have parenthesis *) -> t v -> t u.

  Parameter eval : (bool (* false : disable the parenthesis of [t u]
  *) * (t v (* prefix *) * t v (* suffix *))) * t u -> t v.

  Parameter exec : t u -> t v. (* it is used once at the main point of
  the whole program to retrieve the monadic computation [t v] *)

End PARENTHESIS.

(****************************************************************************)
(** Generic description of a printing of an uplet constructor *)

Module Type CONSTRUCTOR (S : STRING) (M : MONAD_SIMPLE S) (P : PARENTHESIS S M).

  Import M P.

  (* Note that some parameters can be merged (like separator and
    surrounding) but this writting style expansion is rather general *)

  (* For Coq-8.3pl4 and older version: *)
  (*
  Parameter _U :
    bool (* true : the whole need to be protected by a
    parenthesis. Note that this information is a simple hint, the
    constructor which call [_U] can decide not to do so. *) ->
    t v (* prefix *) -> 
    t v (* suffix *) -> 
    forall n, 
    vector (t v) n -> (* separator *)
    vector (bool (* true : follow the same choice as the parenthesis
    hint (indicated by the element we are folding), false : explicit
    disable the parenthesis (do not consider the hint) *) * (t v (*
    prefix *) * t v (* suffix *))) (S n) -> (* surrounding *)
    t u ^^ (S n) --> t u.
    *)

  (* For Coq-8.4: *)
  Parameter _U :
    bool (* true : the whole need to be protected by a
    parenthesis. Note that this information is a simple hint, the
    constructor which call [_U] can decide not to do so. *) ->
    t v (* prefix *) -> 
    t v (* suffix *) -> 
    forall n, 
    Vector.t (t v) n -> (* separator *)
    Vector.t (bool (* true : follow the same choice as the parenthesis
    hint (indicated by the element we are folding), false : explicit
    disable the parenthesis (do not consider the hint) *) * (t v (*
    prefix *) * t v (* suffix *))) (S n) -> (* surrounding *)
    t u ^^ (S n) --> t u.
  

  (* These specials constructors need to have a special implementation
  (not using [_U] for example). *)
  Parameter _positive : positive -> t u.
  Parameter _Z : Z -> t u.
  Parameter _ident : positive -> t u.
  Parameter _float : float -> t u.
  Parameter _int : int -> t u.
  Parameter _int64 : int64 -> t u.
  Parameter _bool : bool -> t u.
  Parameter _prod : forall A B, (A -> t u) -> (B -> t u) -> prod A B -> t u.
  Parameter _list : forall A, (A -> t u) -> list A -> t u.
  Parameter _option : forall A, (A -> t u) -> option A -> t u.
  Parameter map_stringTable : forall A, list A -> list (A * option S.t).

End CONSTRUCTOR.

Module Type CONSTRUCTOR_EXP (S : STRING) (M : MONAD_SIMPLE S)
  (P : PARENTHESIS S M).
  Import M P.
  Parameter _type : type -> t u.
  Parameter _typelist : typelist -> t u.
End CONSTRUCTOR_EXP.

(****************************************************************************)
(** The pretty-printing is done inside this module : for each type, we
explicitly write the name of the corresponding constructor inside a
"string". *)

Module Constructor (S : STRING) (M : MONAD_SIMPLE S) (P : PARENTHESIS S M)
  (C : CONSTRUCTOR S M P). 

  Import Rec Rec_weak M P C.

  Open Scope string_scope.

(* For Coq-8.3pl4 and older version: *)
  (*
  Notation "[| a ; .. ; b |]" := (Vcons _ a _ .. (Vcons _ b _ (Vnil _)) ..).
  *)
  (* For Coq-8.4: *)

  Notation "[| a ; .. ; b |]" := (Vector.cons _ a _ .. (Vector.cons _ b _ (Vector.nil _)) ..).

  Notation "[]" := nil.
  Notation "[ a ; .. ; b ]" := (a :: .. (b :: []) ..).
  Notation "'\n'" := indent.

  Coercion S.of_string : String.string >-> S.t.

  Notation "a ++ b" := (S.append a b).

  Definition ret_u s := ret_u false (print s).

  Section pr. (* Additional constructors (same as [_U]) are defined here *)

    Definition ret {A} := ret A.

    Definition eq_zero n :=
      match n with 
        | 0%nat => true
        | _ => false
      end.
  
    Definition not_b (b : bool) := if b then false else true.

    Definition surr_empty n :=
      Vector.init n (fun _ => (true, (ret tt, ret tt))).

    Definition _U_constr : S.t (* name of the constructor *) ->
      forall n, t u ^^ n --> t u.

    Proof.
      intros s n.
      case_eq n ; intros.
      apply ncurry.
      intros. exact (ret_u s).
      clear n H ; rename n0 into n.
      apply (_U true (print (s ++ " ")) (ret tt)).
      induction n.
      (* For Coq-8.3pl4 and older version: *)
      (* exact (Vnil _). 
         apply Vcons. *)

      (* For Coq-8.4: *)
      exact (@Vector.nil _).
      apply Vector.cons. 
      exact (print " "). trivial.
      apply surr_empty.
    Defined.

    Definition _U_infix2 : t v -> t u ^^ 2 --> t u.

    Proof.
      intros s ; refine (_U true (ret tt) (ret tt) _ [| s |] _).
      apply surr_empty.
    Defined.

    Definition _U_infix2_rass : t v -> t u ^^ 2 --> t u.

    Proof.
      intros s ; refine (_U true (ret tt) (ret tt) _ [| s |]
        [| (true, (ret tt, ret tt)) ; (false, (ret tt, ret tt)) |]).
    Defined.

    Definition _U_infix3 : t v -> t v -> t u ^^ 3 --> t u.

    Proof.
      intros s1 s2 ; refine (_U true (ret tt) (ret tt) _ [| s1 ; s2 |] _).
      apply surr_empty.
    Defined.

    (* For Coq-8.3pl4 and older version: *)
    (* Definition _R : forall n, vector S.t n -> t u ^^ n --> t u.
    Proof.
      intros n l.
      case_eq n ; intros.
      apply ncurry.
      intros. exact (ret_u "{||}").

      apply (_U false (perform [ save_pos ; print "{| "] )
        (perform [ print " |}" ; delete_pos ]) ).
      apply Vector.init. exact (fun _ => perform [ \n ; print " ; " ]).
      subst n.
      refine (Vector.map _ _ l) ; clear.
      intros x.
      exact (false, (print (x ++ " := "), ret tt)).
    Defined.
    *)

    (* For Coq-8.4: *)

    Definition _R : forall n, Vector.t S.t n -> t u ^^ n --> t u.

    Proof.
      intros n l.
      case_eq n ; intros.
      apply ncurry.
      intros. exact (ret_u "{||}").
      apply (_U false (perform [ save_pos ; print "{| "] )
        (perform [ print " |}" ; delete_pos ]) ).
      apply Vector.init. exact (fun _ => perform [ \n ; print " ; " ]).
      subst n.
      refine (Vector.map _ _ l) ; clear.
      intros x.
      exact (false, (print (x ++ " := "), ret tt)).
    Defined.

    (* For Coq-8.3pl4 and older version: *)
    (* Definition _U2 : S.t -> forall n, vector bool (S n) -> t u ^^ (S n) --> t u.
       *)
    (* For Coq-8.4: *)
    Definition _U2 : S.t -> forall n, Vector.t bool (S n) -> t u ^^ (S n) --> t u.

    Proof.
      intros s n l.
      apply (_U (not_b (eq_zero n)) (print (s ++ " ")) (ret tt) _
        (Vector.init _ (fun _ => print " "))).
      refine (Vector.map _ _ l) ; intros.
      refine (H, _).  
      case_eq H ; intros.
      exact (ret tt, ret tt).
      exact (save_pos, delete_pos).
    Defined.

  End pr.

  (* For Coq-8.3pl4 and older version: *)
  (*
  Notation "{{ a ; .. ; b }}" := (_R _
    (Vcons _ (S.of_string a) _ .. (Vcons _ (S.of_string b) _ (Vnil _)) ..)). *)
  (* For Coq-8.4: *)
  Notation "{{ a ; .. ; b }}" := (_R _
    (Vector.cons _ (S.of_string a) _ .. (Vector.cons _ (S.of_string b) _ (Vector.nil _)) ..)).
  Notation "'!' x" := (_U_constr x _) (at level 9).
  Notation "| x · y" := (_U2 x _ y) (at level 9).

  Definition _init_data := _init_data _int _float _Z _ident
    ! "Init_int8"
    ! "Init_int16"
    ! "Init_int32"
    ! "Init_float32"
    ! "Init_float64"
    ! "Init_space"
    ! "Init_addrof".

  Module _AST.

    Definition _globvar {B} f_b := @_AST._globvar _ B _list _bool f_b _init_data
      {{ "gvar_info" ; "gvar_init" ; "gvar_readonly" ; "gvar_volatile" }}.

    (* Definition _program {B C} f_b f_c := @_AST._program _ B C _prod _list f_b f_c _ident _init_data _globvar
       {{ "prog_funct" ; "prog_main" ; "prog_vars" }}.*)

    Definition _program_ : forall B C : Type,
      (B -> t u) -> (C -> t u) -> AST.program B C -> t u.

    Proof.
      intros. eapply _AST._program2. eexact _prod. eexact _list.
      cut (forall A : Type, (A -> S.t -> t u) -> list A -> t u).
      intros. apply (X2 A). intros.
      refine (P.ret_u true (perform [_ ; indent ; _])).
      exact (print X6). apply P.eval. exact (true, (ret tt, ret tt), X3 X5).
      exact X4.
      intros. generalize (map_stringTable _ X3); intros.
      apply (_list _ (fun (a_b : _ * _) => let (a, b) := a_b in X2 a b)).
      refine (List.map _ X4).
      intros (a, o). case_eq o ; intros. exact (a, "(*" ++ t0 ++ "*)").
      exact (a, S.of_string "").
      eexact X. eexact X0. exact _ident. 
      apply _init_data. exact _globvar.
      exact {{ "prog_funct" ; "prog_main" ; "prog_vars" }}.
      trivial.
    Defined.

    Definition _program {B C} := _program_ B C.

    Definition _typ := _AST._typ
      ! "AST.Tint"
      ! "AST.Tfloat".

    Definition _signature := _AST._signature _list _option _typ
      {{ "sig_args" ; "sig_res" }}.

    Definition _memory_chunk := _AST._memory_chunk
      ! "Mint8signed"
      ! "Mint8unsigned"
      ! "Mint16signed"
      ! "Mint16unsigned"
      ! "Mint32"
      ! "Mfloat32"
      ! "Mfloat64".

    Definition _external_function :=
      @_AST._external_function _ _list _ident _memory_chunk _signature _Z _int _typ
      ! "EF_external"
      ! "EF_builtin"
      ! "EF_vload"
      ! "EF_vstore"
      ! "EF_vload_global"
      ! "EF_vstore_global"
      ! "EF_malloc"
      ! "EF_free"
      ! "EF_memcpy"
      ! "EF_annot"
      ! "EF_annot_val".

  End _AST.

  Module _Values.
    Definition _block := _Z.
    Definition _val := @_Values._val _ _int _float _block
      ! "Vundef"
      ! "Vint"
      ! "Vfloat"
      ! "Vptr".
  End _Values.

  Definition _signedness := _signedness 
    ! (*"Signed"*) "++" 
    ! (*"Unsigned"*) "--".

  (* 1.9 -> 1.11 type "intsize" add constructor "IBool". See Csyntax.v *)
  Definition _intsize := _intsize 
    ! "I8"
    ! "I16" 
    ! "I32"
    ! "IBool".

  Definition _floatsize := _floatsize 
    ! "F32"
    ! "F64".

  Definition _attr :=_attr _bool
      {{ "attr_volatile" }}.

  Definition _type_ T (ty : forall A : Type,
    _type_ A (T -> A) 
    (fun ty : Type =>
      (intsize -> A) ->
      (signedness -> A) ->
      (floatsize -> A) -> (Z -> A) -> (ident -> A) -> 
      (attr -> A) ->ty) ) :=
  ty _ _intsize _signedness _floatsize _Z _ident _attr
  ! "Tvoid"
  ! "Tint"
  ! "Tfloat"
  ! (*"Tpointer"*) "`*`"
  ! "Tarray"
  ! "Tfunction"
  ! "Tstruct"
  ! "Tunion"
  ! "Tcomp_ptr"
  ! "Tnil"
  (*! "Tcons"*) (_U_infix2_rass (print " :T: "))
  ! "Fnil"
  ! "Fcons".

  Definition _type := _type_ _ (@_type).

  Definition _typelist := _type_ _ (@_typelist).

  Module Make (Import CE : CONSTRUCTOR_EXP S M P).

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

    Definition _incr_or_decr := _incr_or_decr
      ! "Incr"
      ! "Decr".

    Definition _expr := _expr _Values._val _int _type _ident _unary_operation _binary_operation _Values._block _incr_or_decr
      ! "Eval"
      ! "Evar"
      ! "Efield"
      ! "Evalof"
      ! "Ederef"
      ! "Eaddrof"
      ! "Eunop"
      ! "Ebinop"
      ! "Ecast"
      ! "Econdition"
      ! "Esizeof"
      ! "Ealignof"
      ! "Eassign"
      ! "Eassignop"
      ! "Epostincr"
      ! "Ecomma"
      ! "Ecall"
      ! "Eloc"
      ! "Eparen"
      ! "Enil"
      ! "Econs".

    Definition _label := _ident.

    Definition _statement := _statement _option _expr _label _int
      ! "Sskip"
      ! "Sdo"
    (*! "Ssequence"*) (_U_infix2 (perform [ indent_depth ; print ">> " ]))
    (*! "Sifthenelse"*) (_U true (perform [ save_pos ; print "If " ]) delete_pos _ [| perform [ print " then" ; \n ; print "  " ] ; perform [ \n ; print "else" ; \n ; print "  " ] |] (surr_empty _))
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

    Definition _fundef :=
      _fundef _function _AST._external_function _typelist _type
      ! "Internal"
      | (*! "External"*) "External" · [| true ; false ; true |].

    Definition _program := _AST._program _fundef _type.

  End Make.

End Constructor.

(****************************************************************************)

Module Lazy (S : STRING) (Import M : MONAD_SIMPLE S) <: PARENTHESIS S M.

  Open Scope string_scope.

  Coercion S.of_string : String.string >-> S.t.

  Implicit Arguments bind [A B]. 
  Implicit Arguments ret [A].

  Definition u := (bool * t v) % type.

  Notation "[]" := nil.
  Notation "[ a ; .. ; b ]" := (a :: .. (b :: []) ..).

  Definition eval (a : (bool * (t v * t v)) * t u) : t v := 
    let (a, m) := a in
      let (bb, m1_m2) := a in let (m1, m2) := m1_m2 in
        perform 
        [ m1
          ; bind m (fun b_m => let (b, m) := b_m in
            if andb bb b then perform [ print "(" ; m ; print ")" ] else m)
          ; m2 ].

  Definition ret_u : bool -> t v -> t u := fun b m => ret (b, m).

  Definition exec (m : t u) : t v :=
    bind m (fun b_m => let (_, m) := b_m in m).

End Lazy.

(****************************************************************************)

Module Strict (S : STRING) (Import M : MONAD_SIMPLE S) <: PARENTHESIS S M.

  Open Scope string_scope.

  Coercion S.of_string : String.string >-> S.t.

  Implicit Arguments bind [A B]. 
  Implicit Arguments ret [A].

  Definition u := v.

  Notation "[]" := nil.
  Notation "[ a ; .. ; b ]" := (a :: .. (b :: []) ..).

  Definition eval (a : (bool * (t v * t v)) * t u) : t v := 
    let (a, m) := a in
      let (bb, m1_m2) := a in let (m1, m2) := m1_m2 in
        perform 
        [ m1
          ; print "("
          ; m
          ; print ")"
          ; m2 ].

  Definition ret_u : bool -> t v -> t u := fun b m => m.

  Definition exec (m : t u) : t v := m.

End Strict.

(****************************************************************************)

Module Monad_simple (F : FRESH) (K_type : KEY with Definition t := type)
  (K_typelist : KEY with Definition t := typelist) (S : STRING)
  (B : BUFFER S F) (Map_type : MAP K_type) (Map_typelist : MAP K_typelist)
  <: MONAD_SIMPLE S.

  Require Import Ascii.

  Notation "[]" := nil.
  Notation "[ a ; .. ; b ]" := (a :: .. (b :: []) ..).

  Implicit Arguments Map_type.add [A].
  Implicit Arguments Map_type.find [A].
  Implicit Arguments Map_typelist.add [A].
  Implicit Arguments Map_typelist.find [A].

  Module PositiveMap := FMapAVL.Make OrderedPositive.

  Record st := mk_st
    { buf : B.t
      ; pos : list nat
      ; depth : nat
      ; used_var : PositiveMap.t (S.t * option S.t)
      ; ident : F.t
      ; map_t : Map_type.t F.t
      ; map_tlist : Map_typelist.t F.t }.

  Inductive state {A} := L (_ : A) (_ : st).

  Definition t A := st -> @state A.
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

  Definition get_st f : t unit := fun st =>
    ret tt (f mk_st st).

  Definition print_newline : t unit := get_st (fun f st =>
    f (B.print_newline (buf st)) (pos st) (depth st) (used_var st) (ident st) (map_t st) (map_tlist st)).

  Definition print s : t unit := get_st (fun f st =>
    f (B.print s (buf st)) (pos st) (depth st) (used_var st) (ident st) (map_t st) (map_tlist st)).

  Definition print_type t := get_st (fun f st =>
    match
      match Map_type.find t (map_t st) with
        | None => let i := F.succ (ident st) in
          (i, i, Map_type.add t i)
        | Some i => (ident st, i, fun x => x) 
      end
      with
        (id, i, ff) =>
        f (B.print_ident i (buf st)) (pos st) (depth st) (used_var st) id (ff (map_t st)) (map_tlist st)
    end).

  Definition print_typelist t := get_st (fun f st =>
    match
      match Map_typelist.find t (map_tlist st) with
        | None => let i := F.succ (ident st) in
          (i, i, Map_typelist.add t i)
        | Some i => (ident st, i, fun x => x) 
      end
      with
        (id, i, ff) =>
        f (B.print_ident i (buf st)) (pos st) (depth st) (used_var st) id (map_t st) (ff (map_tlist st))
    end).

  Definition add_depth : t unit := get_st (fun f st => 
    f (buf st) (pos st) (S (depth st)) (used_var st) (ident st) (map_t st) (map_tlist st)).

  Definition remove_depth : t unit := get_st (fun f st =>
    f (buf st) (pos st) (match depth st with 0 => 0 | S n => n end % nat) (used_var st) (ident st) (map_t st) (map_tlist st)). 

  Definition save_pos : t unit := get_st (fun f st =>
    let buf_st := buf st in
      f buf_st (B.pos buf_st :: pos st) (depth st) (used_var st) (ident st) (map_t st) (map_tlist st)).

  Definition add_used_var p s : t unit := get_st (fun f st =>
    f (buf st) (pos st) (depth st) (PositiveMap.add p s (used_var st)) (ident st) (map_t st) (map_tlist st)).

  Definition indent_ f : t unit :=
    fun st =>
      perform
      [ print_newline
        ; print (S.make (f st match pos st with
                                | [] => 0
                                | x :: _ => x
                              end % nat) " " % char) ] st.

  Definition indent : t unit := indent_ (fun _ x => x).

  Definition indent_depth : t unit := indent_ (fun st => plus (2 * depth st)).

  Definition delete_pos : t unit := fun st =>
    ret tt (mk_st (buf st) (List.tail (pos st)) (depth st) (used_var st) (ident st) (map_t st) (map_tlist st)).

  Definition tt := tt.

End Monad_simple.

(****************************************************************************)

Module Monad_list (S : STRING) (U : UTIL S) (Import M : MONAD_SIMPLE S)
  (Import L : PARENTHESIS S M) <: CONSTRUCTOR S M L.

  Open Scope string_scope.

  Coercion S.of_string : String.string >-> S.t.

  Notation "a ++ b" := (S.append a b).
  (* For Coq-8.3pl4 and older version: *)
  (* Notation "{{ a ; .. ; b }}" := (Vcons _ a _ .. (Vcons _ b _ (Vnil _)) ..).*)
  (* For Coq-8.4: *)
  Notation "{{ a ; .. ; b }}" := (Vector.cons _ a _ .. (Vector.cons _ b _ (Vector.nil _)) ..).
  Notation "[]" := nil.
  Notation "[ a ; .. ; b ]" := (a :: .. (b :: []) ..).

  Implicit Arguments ret [A].

  (* For Coq-8.3pl4 and older version: *)
  (*
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
  Proof.
  intros.
  case_eq l. tauto.
  intros x xs _.
  refine (ret_u b _) ; clear b.
  (* (* put this below to display the depth as a Coq comment *)  
    fun st => print ("(*" ++ (String (ascii_of_nat (depth st + 48)) EmptyString) ++ "*)") st ; *)
  refine (perform [ add_depth ; pref ; _ ; suff ; remove_depth ]) ; clear pref suff.
  inversion surr ; clear surr ; rename X into surr.
  refine (_ (eval (a, x))) ; clear a x n0 H1.
  pose (v_to_list A v := let (l, _) := Vector.to_list A n v in l).
  refine (List.fold_left _ (List.combine (v_to_list _ sep) (List.combine (v_to_list _ surr) xs) )) ; clear sep surr xs.
  intros acc (sep, a).
  exact (perform [ acc ; sep ; eval a ]).
  Defined.
    *)
  (* For Coq-8.4: *)
  Definition _U_aux : forall
    (b : bool)
    (pref : t v)
    (suff : t v)
    (n : nat)
    (sep : Vector.t (t v) n)
    (surr : Vector.t (bool * (t v * t v)) (S n))
    (l : list (t u))
    (_ : l <> nil),
    t u.
  Proof.
  intros.
  case_eq l. tauto.
  intros x xs _.
  refine (ret_u b _) ; clear b.
  (* (* put this below to display the depth as a Coq comment *)  
    fun st => print ("(*" ++ (String (ascii_of_nat (depth st + 48)) EmptyString) ++ "*)") st ; *)
  refine (perform [ add_depth ; pref ; _ ; suff ; remove_depth ]) ; clear pref suff.
  inversion surr ; clear surr ; rename X into surr.
  refine (_ (eval (h, x))) ; clear h x n0 H1.
  pose (v_to_list A v := let (l, _) := Vector.to_list A n v in l).
  refine (List.fold_left _ (List.combine (v_to_list _ sep) (List.combine (v_to_list _ surr) xs) )) ; clear sep surr xs.
  intros acc (sep, a).
  exact (perform [ acc ; sep ; eval a ]).
  Defined.

  (* For Coq-8.3pl4 and older version: *)
  (*
  Definition _U : 
    bool -> 
    t v -> 
    t v -> 
    forall n, 
    vector (t v) n -> 
    vector (bool * (t v * t v)) (S n) -> 
    t u ^^ (S n) --> t u.
    *)

  (* For Coq-8.4: *)
  Definition _U : 
    bool -> 
    t v -> 
    t v -> 
    forall n, 
    Vector.t (t v) n -> 
    Vector.t (bool * (t v * t v)) (S n) -> 
    t u ^^ (S n) --> t u.
  
  Proof.
  intros b pref suff n sep surr.
  apply ncurry.
  intro cpl.
  apply (_U_aux b pref suff n sep surr (nprod_to_list _ _ cpl)).
  destruct cpl.
  simpl.
  auto with *.
  Defined.

  Definition _positive p := ret_u false (print ("`" ++ U.string_of_positive p)).

  Definition _Z z := ret_u false (print (U.string_of_Z z)).

  Definition _ident i := 
    match U.name i with
      | Some s => ret_u false (perform [ add_used_var i s ; print (fst s) ])
      | None => _positive i
    end.

  Definition number f_conv (m : t u) := 
    ret_u false (eval (false, (print ("(" ++ f_conv), print ")"), m)).

  Definition _int i := ret_u false (eval (false, (print "`", ret tt), _Z (Int.intval i))).
  Definition _int64 i := number "Int64.repr " (_Z (Int64.intval i)).
  Definition _float f := number "Float.double_of_bits " (_int64 (Float.bits_of_double f)).

  Definition _prod : forall A B, (A -> t u) -> (B -> t u) -> prod A B -> t u.

  Proof.
  intros A B fa fb (a, b).
  eapply (_U_aux false (print "(") (print ")") _ {{ print ", " }} (Vector.init _ (fun _ => (false, (ret tt, ret tt)))) [ fa a ; fb b ]).
  auto with *.
  Defined.

  Definition _list : forall A, (A -> t u) -> list A -> t u.

  Proof.
  intros A f l.
  case_eq l ; intros.
  exact (ret_u false (print "[]")).
  apply (_U_aux false (perform [ save_pos ; print "[ " ]) (perform [ print " ]" ; delete_pos ]) (List.length l) (Vector.init _ (fun _ => perform [ indent ; print "; " ] )) 
    (Vector.init _ (fun _ => (false, (ret tt, ret tt)))) (List.map f l)).
  rewrite H. simpl.
  auto with *.
  Defined.

  Definition _bool (b : bool) := 
    ret_u false (print (if b then "true" else "false")).

  Definition _option : forall A, (A -> t u) -> option A -> t u.

  Proof.
  intros A f l.
  case_eq l ; intros.
  apply (_U_aux true (print "Some ") (ret tt) 1 (Vector.init _ (fun _ => ret tt)) 
    (Vector.init _ (fun _ => (true, (ret tt, ret tt)))) [ f a ]).
  auto with *.
  exact (ret_u false (print "None")).
  Defined.

  Definition map_stringTable := U.map_stringTable.

End Monad_list.

(****************************************************************************)
(** Main function: Given all the OCaml modules, this module produces a
function doing the whole printing of the considered AST *)

Module Main (K_t : KEY with Definition t := type)
  (K_tl : KEY with Definition t := typelist) (Map_t : MAP K_t)
  (Map_tl : MAP K_tl) (S : STRING) (U : UTIL S) (F : FRESH)
  (Map_f : MAP F) (B : BUFFER S F).

  Module M := Monad_simple F K_t K_tl S B Map_t Map_tl.
  Module L := Lazy S M.
  Module C := Monad_list S U M L.
  Module Constructor_list := Constructor S M L C.

  Module M_simpl.
    Definition _type t := L.ret_u false (M.print_type t).
    Definition _typelist t := L.ret_u false (M.print_typelist t).
  End M_simpl.

  Module C_list := Constructor_list.Make M_simpl.

  Import M.

  Open Scope string_scope.

  Coercion S.of_string : String.string >-> S.t.

  Implicit Arguments B.empty [A].
  Implicit Arguments PositiveMap.empty [elt].
  Implicit Arguments Map_t.empty [A].
  Implicit Arguments Map_tl.empty [A].
  Implicit Arguments Map_t.fold [A B].
  Implicit Arguments Map_tl.fold [A B].
  Implicit Arguments Map_f.add [A].
  Implicit Arguments Map_f.fold [A B].

  Notation "[ ]" := nil.
  Notation "[ a ; .. ; b ]" := (a :: .. (b :: []) ..).
  Notation "a ++ b" := (S.append a b).

  Definition coq_output_1 := List.map S.of_string
      [ "(**"
      ; "SimSoC-Cert, a toolkit for generating certified processor simulators"
      ; "See the COPYRIGHTS and LICENSE files."
      ; ""
      ; "Sample CompCert value of type [AST.program fundef type]."
      ; "*)"
      ; ""
      ; "Require Import" 
      ; "  (* compcert *)"
      ; "  Coqlib"
      ; "  Integers"
      ; "  Floats"
      ; "  AST"
      ; "  Values"
      ; "  Csyntax"
      ; "  ."
      ; "Open Scope positive_scope."
      ; ""
      ; "Notation ""` x"" := (Int.repr x) (at level 9)."
      ; "Notation ""[ ]"" := nil."
      ; "Notation ""[ a ; .. ; b ]"" := (a :: .. (b :: []) ..)."
      ; "Notation ""a :T: b"" := (Tcons a b) (at level 9, right associativity)."
      ; "Notation ""`*`"" := Tpointer."
      ; "Notation ""a >> b"" := (Ssequence a b) (at level 9)."
      ; "Notation ""++"" := Signed."
      ; "Notation ""--"" := Unsigned."
      ; "Notation ""'If' a 'then' b 'else' c"" := (Sifthenelse a b c) (at level 9)."
      ; "" ].

  Definition coq_output_2 := List.map S.of_string
      [ ""
      ; "Definition program_fundef_type :=" ].

  Definition coq_output_3 := List.map S.of_string
      [ ""
      ; "." 
      ; "Check program_fundef_type : AST.program fundef type." ].

  Definition b_perform buf l :=
    List.fold_left (fun buf f => B.print_newline (B.print f buf)) l buf.

  Definition buf_of_ {A} f (t : A) :=
    match L.exec (f t) (mk_st (B.empty tt) [] 0 PositiveMap.empty F.zero Map_t.empty Map_tl.empty) with
      L _ st => buf st
    end.

  Definition buf_of_type := buf_of_ Constructor_list._type.

  Definition buf_of_typelist := buf_of_ Constructor_list._typelist.

  Definition program_fundef_type ast := 
    let f buf_ty i :=
      List.fold_left (fun buf f => f buf)
      [ B.print "Definition "
      ; B.print_ident i
      ; B.print " := "
      ; fun b => B.add_buffer b buf_ty
      ; B.print "."
      ; B.print_newline ] in
  match L.exec (C_list._program ast) (mk_st (B.empty tt) [] 0 PositiveMap.empty F.zero Map_t.empty Map_tl.empty) with
    L _ st => 
      let map := Map_t.fold (fun t i => Map_f.add i (Constructor_list._type t)) (map_t st) (Map_f.empty _) in
      let map := Map_tl.fold (fun t i => Map_f.add i (Constructor_list._typelist t)) (map_tlist st) map in
      let (b, u) :=
        Map_f.fold (fun i t (b_u : _ * _) =>
          let (b, u) := b_u in
          match L.exec t (mk_st (B.empty tt) [] 0 u F.zero Map_t.empty Map_tl.empty) with
            L _ st => (f (buf st) i b, used_var st)
          end) map (B.empty tt, used_var st) in

      b_perform (B.add_buffer (b_perform (B.add_buffer (List.fold_left b_perform 
      [ coq_output_1 
      ; List.map (fun p_s : (_ * (_ * _)) => let (p, s_o) := p_s in let (s, o) := s_o in
          "Definition " ++ s ++ " := " ++ U.string_of_positive p ++ "." ++ match o with Some s => " (* " ++ s ++ " *)" | None => "" end
        ) (PositiveMap.elements u) ] (B.empty tt) ) b
      ) coq_output_2) 
      (buf st)
      ) coq_output_3
  end.

End Main.
