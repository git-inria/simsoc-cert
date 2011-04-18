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
(* type of an expression *)

Definition type_of_expr e :=
  match e with
    | Eval _ t
    | Evar _ t
    | Efield _ _ t
    | Evalof _ t
    | Ederef _ t
    | Eaddrof _ t
    | Eunop _ _ t
    | Ebinop _ _ _ t
    | Ecast _ t
    | Econdition _ _ _ t
    | Esizeof _ t
    | Eassign _ _ t
    | Eassignop _ _ _ _ t
    | Epostincr _ _ t
    | Ecomma _ _ t
    | Ecall _ _ t
    | Eloc _ _ t
    | Eparen _ t => t
  end.

(****************************************************************************)
(* untyped expressions *)

Inductive exp : Type :=
  | Dval (v: val) (ty: type)
  | Dvar (x: ident) (ty: type)
  | Dfield (l: exp) (f: ident)
  | Dvalof (l: exp)
  | Dderef (r: exp)
  | Daddrof (l: exp)
  | Dunop (op: unary_operation) (r: exp)
  | Dbinop (op: binary_operation) (r1 r2: exp)
  | Dcast (r: exp) (ty: type)
  | Dcondition (r1 r2 r3: exp)
  | Dsizeof (ty': type)
  | Dassign (l: exp) (r: exp)
  | Dassignop (op: binary_operation) (l: exp) (r: exp)
  | Dpostincr (id: incr_or_decr) (l: exp)
  | Dcomma (r1 r2: exp)
  | Dcall (r1: exp) (rargs: list exp)
  | Dloc (b: block) (ofs: int).

Fixpoint field_type id fs :=
  match fs with
    | Fnil => None
    | Fcons id' t fs' =>
      match ident_eq id id' with
        | left _ => Some t
        | right _ => field_type id fs'
      end
  end.

Fixpoint type_of_exp e :=
  match e with
  | Dval v t => Some t
  | Dvar x t => Some t
  | Dfield e id =>
    match type_of_exp e with
      | Some (Tstruct _ fs) => field_type id fs
      | _ => None
    end
  | Dvalof e => type_of_exp e
  | Dderef e =>
    match type_of_exp e with
      | Some (Tpointer t) => Some t
      | _ => None
    end
  | Daddrof e =>
    match type_of_exp e with
      | Some t => Some (Tpointer t)
      | _ => None
    end
  | Dunop _ e => type_of_exp e
  | Dbinop _ e1 e2 => type_of_exp e1
  | Dcast _ t => Some t
  | Dcondition _ e2 e3 => type_of_exp e2
  | Dsizeof t => None
  | Dassign e1 _ => type_of_exp e1
  | Dassignop _ e1 _ => type_of_exp e1
  | Dpostincr _ e => type_of_exp e
  | Dcomma _ e2 => type_of_exp e2
  | Dcall e _ =>
    match type_of_exp e with
      | Some (Tfunction _ t) => Some t
      | _ => None
    end
  | Dloc _ _ => None
  end.

Fixpoint exprlist_of_list_expr es :=
  match es with
    | nil => Enil
    | e :: es' => Econs e (exprlist_of_list_expr es')
  end.

Section opt.

  Variables f : exp -> option expr.

  Fixpoint opts_aux es ds :=
    match ds with
      | nil => Some (exprlist_of_list_expr (rev es))
      | d :: ds' =>
        match f d with
          | Some e => opts_aux (e :: es) ds'
          | _ => None
        end
    end.

  Definition opts := opts_aux nil.

End opt.

Fixpoint expr_of_exp d :=
  match type_of_exp d with
    | None => None
    | Some t =>
      match d with
        | Dval v t => Some (Eval v t)
        | Dvar id t => Some (Evar id t)
        | Dfield d' id =>
          match expr_of_exp d' with
            | Some e => Some (Efield e id t)
            | _ => None
          end
        | Dvalof d' =>
          match expr_of_exp d' with
            | Some e => Some (Evalof e t)
            | _ => None
          end
        | Dderef d' =>
          match expr_of_exp d' with
            | Some e => Some (Ederef e t)
            | _ => None
          end
        | Daddrof d' =>
          match expr_of_exp d' with
            | Some e => Some (Eaddrof e t)
            | _ => None
          end
        | Dunop o d' =>
          match expr_of_exp d' with
            | Some e => Some (Eunop o e t)
            | _ => None
          end
        | Dbinop o d1 d2 =>
          match expr_of_exp d1, expr_of_exp d2 with
            | Some e1, Some e2 => Some (Ebinop o e1 e2 t)
            | _, _ => None
          end
        | Dcast d' _ =>
          match expr_of_exp d' with
            | Some e => Some (Ecast e t)
            | _ => None
          end
        | Dcondition d1 d2 d3 =>
          match expr_of_exp d1, expr_of_exp d2, expr_of_exp d3 with
            | Some e1, Some e2, Some e3 => Some (Econdition e1 e2 e3 t)
            | _, _, _ => None
          end
        | Dsizeof t' => Some (Esizeof t' t) 
        | Dassign d1 d2 =>
          match expr_of_exp d1, expr_of_exp d2 with
            | Some e1, Some e2 => Some (Eassign e1 e2 t)
            | _, _ => None
          end
        | Dassignop o d1 d2 =>
          match expr_of_exp d1, expr_of_exp d2 with
            | Some e1, Some e2 => Some (Eassignop o e1 e2 t t)
            | _, _ => None
          end
        | Dpostincr o d' =>
          match expr_of_exp d' with
            | Some e => Some (Epostincr o e t)
            | _ => None
          end
        | Dcomma d1 d2 =>
          match expr_of_exp d1, expr_of_exp d2 with
            | Some e1, Some e2 => Some (Ecomma e1 e2 t)
            | _, _ => None
          end
        | Dcall d' ds =>
          match expr_of_exp d', opts expr_of_exp ds with
            | Some e, Some es => Some (Ecall e es t)
            | _, _ => None
          end
        | Dloc b i => Some (Eloc b i t)
      end
  end.

(****************************************************************************)
(** coercions *)

Coercion Int.repr : Z >-> int.
Coercion Vint : int >-> val.
Coercion Sdo : expr >-> statement.
Coercion init_data_of_ascii : ascii >-> init_data.
Coercion list_init_data_of_string : string >-> list.

(****************************************************************************)
(* notations *)

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

Notation "a -: b" := (pair a b) (at level 60).

Notation "a :E: b" := (Econs a b) (at level 70, right associativity).
Notation "E[ ]" := Enil.
Notation "E[ a ; .. ; b ]" := (a :E: .. (b :E: Enil) ..).

Notation "! x `: t" := (Eunop Onotbool x t) (at level 30).
Notation "`~ x `: t" := (Eunop Onotint x t) (at level 30).
Notation "- x `: t" := (Eunop Oneg x t) (at level 30).

Notation "x + y `: t" := (Ebinop Oadd x y t) (at level 20).
Notation "x - y `: t" := (Ebinop Osub x y t) (at level 20).
Notation "x * y `: t" := (Ebinop Omul x y t) (at level 20).
Notation "x / y `: t" := (Ebinop Odiv x y t) (at level 20).
Notation "x % y `: t" := (Ebinop Omod x y t) (at level 20).
Notation "x & y `: t" := (Ebinop Oand x y t) (at level 20).
Notation "x || y `: t" := (Ebinop Oor x y t) (at level 20).
Notation "x ^ y `: t" := (Ebinop Oxor x y t) (at level 20).
Notation "x << y `: t" := (Ebinop Oshl x y t) (at level 20).
Notation "x >> y `: t" := (Ebinop Oshr x y t) (at level 20).
Notation "x == y `: t" := (Ebinop Oeq x y t) (at level 20).
Notation "x != y `: t" := (Ebinop One x y t) (at level 20).
Notation "x < y `: t" := (Ebinop Olt x y t) (at level 20).
Notation "x > y `: t" := (Ebinop Ogt x y t) (at level 20).
Notation "x <= y `: t" := (Ebinop Ole x y t) (at level 20).
Notation "x >= y `: t" := (Ebinop Oge x y t) (at level 20).

Notation "`* e `: t" := (Ederef e t) (at level 20).
Notation "# v `: t" := (Eval v t) (at level 20).
Notation "$ id `: t" := (Evar id t) (at level 20).
Notation "\ id `: t" := (Evalof (Evar id t) t) (at level 20).
Notation "& e `: t" := (Eaddrof e t) (at level 20).
Notation "e1 ? e2 `| e3 `: t" := (Econdition e1 e2 e3 t) (at level 20).
Notation "e -- `: t" := (Epostincr Decr e t) (at level 20).
Notation "e ++ `: t" := (Epostincr Incr e t) (at level 20).
Notation "e1 `= e2 `: t" := (Eassign e1 e2 t) (at level 8).
Notation "e | id `: t" := (Efield e id t) (at level 20).

Notation "x += y `: t1 `: t2" := (Eassignop Oadd x y t1 t2) (at level 8).
Notation "x -= y `: t1 `: t2" := (Eassignop Osub x y t1 t2) (at level 8).
Notation "x *= y `: t1 `: t2" := (Eassignop Omul x y t1 t2) (at level 8).
Notation "x /= y `: t1 `: t2" := (Eassignop Odiv x y t1 t2) (at level 8).
Notation "x %= y `: t1 `: t2" := (Eassignop Omod x y t1 t2) (at level 8).
Notation "x &= y `: t1 `: t2" := (Eassignop Oand x y t1 t2) (at level 8).
Notation "x |= y `: t1 `: t2" := (Eassignop Oor x y t1 t2) (at level 8).
Notation "x ^= y `: t1 `: t2" := (Eassignop Oxor x y t1 t2) (at level 8).

Definition lscase a := LScase (fst a) (snd a).
Notation "a :L: b" := (lscase a b) (at level 70, right associativity).
Notation "L[ ]" := LSdefault.
Notation "L[ a ; .. ; b ]" := (a :L: .. (b :L: Fnil) ..).

Notation "a ;; b" := (Ssequence a b) (at level 51, right associativity).
Notation "`if a 'then' b 'else' c" := (Sifthenelse a b c) (at level 9).
Notation "'while' a '`do' b" := (Swhile a b) (at level 19).
Notation "'`do' a 'while' b" := (Sdowhile b a) (at level 19).
Notation "'return'" := (Sreturn).
Notation "'goto'" := (Sgoto).
Notation "'label' l `: s" := (Slabel l s) (at level 5).
Notation "'switch' e { ls }" := (Sswitch e ls) (at level 7).
Notation "'default'-: s" := (LSdefault s) (at level 5).
Notation "'continue'" := (Scontinue).
Notation "'break'" := (Sbreak).
Notation "'for' ( s1 , e , s2 ) { s3 }" := (Sfor s1 e s2 s3) (at level 19).
Notation "'skip'" := (Sskip).
