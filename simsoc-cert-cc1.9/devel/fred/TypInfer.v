(**
SimSoC-Cert, a toolkit for generating certified processor simulators.

See the COPYRIGHTS and LICENSE files.

Type inference.
*)

(*WARNING: incomplete development! *)

Set Implicit Arguments.

Require Import List.
Require Import Csyntax Values AST Integers.

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
