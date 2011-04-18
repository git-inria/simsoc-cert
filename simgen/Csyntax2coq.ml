(**
SimSoC-Cert, a toolkit for generating certified processor simulators
See the COPYRIGHTS and LICENSE files.

Pretty print CompCert type [AST.program fundef type] to Coq.
*)

open AST;;
open Values;;
open Csyntax;;
open Datatypes;;
open Printf;;
open Camlcoq;;

(*****************************************************************************)
(** basic OCaml data structures *)

type 'a bprint = Buffer.t -> 'a -> unit;;
type 'a fprint = out_channel -> 'a -> unit;;

let fprint f oc x =
  let b = Buffer.create 100 in
    f b x; fprintf oc "%s" (Buffer.contents b);;

let sprint f x =
  let b = Buffer.create 100 in
    f b x; sprintf "%s" (Buffer.contents b);;

let string b s = bprintf b "%s" s;;
let int b i = bprintf b "%d" i;;
let int32 b i = bprintf b "%ld" i;;

let pair f sep g b (x, y) = bprintf b "%a%s%a" f x sep g y;;
let first f b (x,_) = f b x;;
let second f b (_,x) = f b x;;

let par f b x = bprintf b "(%a)" f x;;

let prefix s f b x = bprintf b "%s%a" s f x;;
let postfix s f b x = bprintf b "%a%s" f x s;;
let endline f b x = postfix "\n" f b x;;

let list_iter elt b = List.iter (elt b);;

let list sep elt =
  let rec aux b = function
    | [] -> ()
    | [x] -> elt b x
    | x :: l -> bprintf b "%a%s%a" elt x sep aux l
  in aux;;

let list_nil nil sep elt =
  let rec aux b = function
    | [] -> bprintf b "%s" nil
    | x :: l -> bprintf b "%a%s%a" elt x sep aux l
  in aux;;

let plist f b = function
  | [] -> f b []
  | l -> par f b l;;

let using string_of_elt b x = string b (string_of_elt x);;

let app1 b s f1 v1 = bprintf b "%s %a" s f1 v1;;
let app2 b s f1 v1 f2 v2 = bprintf b "%s %a %a" s f1 v1 f2 v2;;
let app3 b s f1 v1 f2 v2 f3 v3 =
  bprintf b "%s %a %a %a" s f1 v1 f2 v2 f3 v3;;
let app4 b s f1 v1 f2 v2 f3 v3 f4 v4 =
  bprintf b "%s %a %a %a %a" s f1 v1 f2 v2 f3 v3 f4 v4;;
let papp5 b s f1 v1 f2 v2 f3 v3 f4 v4 f5 v5 =
  bprintf b "%s %a %a %a %a %a" s f1 v1 f2 v2 f3 v3 f4 v4 f5 v5;;

let papp1 b s f1 v1 = bprintf b "(%s %a)" s f1 v1;;
let papp2 b s f1 v1 f2 v2 = bprintf b "(%s %a %a)" s f1 v1 f2 v2;;
let papp3 b s f1 v1 f2 v2 f3 v3 =
  bprintf b "(%s %a %a %a)" s f1 v1 f2 v2 f3 v3;;
let papp4 b s f1 v1 f2 v2 f3 v3 f4 v4 =
  bprintf b "(%s %a %a %a %a)" s f1 v1 f2 v2 f3 v3 f4 v4;;
let papp5 b s f1 v1 f2 v2 f3 v3 f4 v4 f5 v5 =
  bprintf b "(%s %a %a %a %a %a)" s f1 v1 f2 v2 f3 v3 f4 v4 f5 v5;;

let todo b _ = string b "TODO";;

(*****************************************************************************)
(** Coq header *)

let header = "\
(**\n\
SimSoC-Cert, a toolkit for generating certified processor simulators\n\
See the COPYRIGHTS and LICENSE files.\n\
\n\
Coq representation of a C program automatically generated by Simgen.\n\
*)\n\
\n\
Require Import Cnotations.\n\
\n\
Open Scope positive_scope.\n";;

(*****************************************************************************)
(** basic Coq data structures *)

let bool b = bprintf b "%b";;

let option elt b = function
  | None -> bprintf b "None"
  | Some x -> bprintf b "Some %a" elt x;;

let coq_list elt b = function
  | [] -> bprintf b "[]"
  | x :: l -> bprintf b "[%a%a]" elt x (list "" (prefix "; " elt)) l;;

let coq_list_sep sep elt b = function
  | [] -> bprintf b "[]"
  | x :: l -> bprintf b "[%a%a]" elt x (list "" (prefix (";" ^ sep) elt)) l;;

let coq_pair f g b (Coq_pair (x, y)) = bprintf b "(%a,%a)" f x g y;;

let coq_Z b x = int32 b (camlint_of_z x);;

let int b x = int32 b (camlint_of_coqint x);;

let positive b x = int32 b (camlint_of_positive x);;

let float = todo;;

let float32 = todo;;

let float64 = todo;;

(*****************************************************************************)
(** ident *)

let remove_prefix p s =
  let k = String.length p and n = String.length s in
    if n >= k && String.sub s 0 k = p then "_" ^ String.sub s k (n-k) else s;;

let valid_coq_ident s =
(*  let s = remove_prefix "struct " (remove_prefix "union " s) in*)
    match s with
      | "end" as s -> "_" ^ s
      | _ ->
	  for i = 0 to String.length s - 1 do
	    if s.[i] = '$' || s.[i] = ' ' then s.[i] <- '_'
	  done;
	  s;;

let identTable = Hashtbl.create 57;;

let add_ident id s = Hashtbl.add identTable id (valid_coq_ident s);;

let init_identTable () = Hashtbl.iter add_ident string_of_atom;;

let string_of_ident id =
  try Hashtbl.find identTable id
  with Not_found ->
    Printf.sprintf "unknown_atom_%ld" (camlint_of_positive id);;

let ident = using string_of_ident;;

let identifiers b =
  bprintf b "\n(* identifiers *)\n\n";
  Hashtbl.iter
    (fun id s -> bprintf b "Definition %s := %a.\n" s positive id)
    identTable;;

(*****************************************************************************)
(** signature *)

let string_of_typ = function
  | AST.Tint -> "AST.Tint"
  | AST.Tfloat -> "AST.Tfloat";;

let typ = using string_of_typ;;

let signature b s =
  bprintf b "{| sig_args := %a; sig_res := %a |}"
    (coq_list typ) s.sig_args (option typ) s.sig_res;;

(*****************************************************************************)
(** type *)

let string_of_signedness = function
  | Signed -> "Signed"
  | Unsigned -> "Unsigned";;

let signedness = using string_of_signedness;;

let string_of_intsize = function
  | I8 -> "I8"
  | I16 -> "I16"
  | I32 -> "I32";;

let intsize = using string_of_intsize;;

let string_of_floatsize = function
  | F32 -> "F32"
  | F64 -> "F64";;

let floatsize = using string_of_floatsize;;

let rec types_of_typelist = function
  | Tnil -> []
  | Tcons (t, tl) -> t :: types_of_typelist tl;;

let rec fields_of_fieldlist = function
  | Fnil -> []
  | Fcons (id, t, fl) -> (id,t) :: fields_of_fieldlist fl;;

module TypOrd = struct
  type t = coq_type
  let compare = Pervasives.compare
end;;

module TypMap = Map.Make (TypOrd);;

let typMap = ref TypMap.empty;;

type kind = Union | Struct;;

let coq_type_of_kind k id fl =
  match k with
    | Union -> Tunion (id, fl)
    | Struct -> Tstruct (id, fl);;

let add_type_kind k id fl =
  let t = coq_type_of_kind k id fl in
    try TypMap.find t !typMap
    with Not_found ->
      let s = string_of_ident id in
	typMap := TypMap.add t s !typMap;
	s;;

let rec coq_type b = function
  | Tvoid -> string b "void"
  | Tint (I8, Signed) -> string b "int8"
  | Tint (I8, Unsigned) -> string b "uint8"
  | Tint (I16, Signed) -> string b "int16"
  | Tint (I16, Unsigned) -> string b "uint16"
  | Tint (I32, Signed) -> string b "int32"
  | Tint (I32, Unsigned) -> string b "uint32"
  | Tfloat F32 -> string b "float32"
  | Tfloat F64 -> string b "float64"
  | Tpointer t -> app1 b "`*`" coq_type_ref t
  | Tarray (t, n) -> app2 b "Tarray" coq_type_ref t coq_Z n
  | Tfunction (tl, t) -> app2 b "Tfunction" typelist tl coq_type_ref t
  | Tstruct (id, fl) -> app2 b "Tstruct" ident id fieldlist fl
  | Tunion (id, fl) -> app2 b "Tunion" ident id fieldlist fl
  | Tcomp_ptr id -> app1 b "Tcomp_ptr" ident id

and pcoq_type b t =
  match t with
  | Tvoid
  | Tint _
  | Tfloat _ -> coq_type b t
  | Tpointer _
  | Tarray _
  | Tfunction _
  | Tstruct _
  | Tunion _
  | Tcomp_ptr _ -> par coq_type b t

and typelist b tl =
  bprintf b "T%a" (coq_list coq_type) (types_of_typelist tl)

and fieldlist b fl =
  bprintf b "\nF%a" (coq_list_sep "\n  " field) (fields_of_fieldlist fl)

and field b = pair ident " -: " coq_type b

and coq_type_ref b t =
  match t with
    | Tvoid
    | Tint _
    | Tfloat _
    | Tpointer _
    | Tarray _
    | Tfunction _
    | Tcomp_ptr _ -> coq_type b t
    | Tstruct (id, fl) -> prefix "typ_" string b (add_type_kind Struct id fl)
    | Tunion (id, fl) -> prefix "typ_" string b (add_type_kind Union id fl)

and typelist_ref b tl =
  bprintf b "T%a" (coq_list coq_type_ref) (types_of_typelist tl)

and fieldlist_ref b fl =
  bprintf b "F%a" (coq_list field_ref) (fields_of_fieldlist fl)

and field_ref b = pair ident "`:" coq_type_ref b;;

let pcoq_type_ref b t =
  match t with
    | Tvoid
    | Tint _
    | Tfloat _ -> coq_type_ref b t
    | Tpointer _
    | Tarray _
    | Tfunction _
    | Tcomp_ptr _
    | Tstruct _
    | Tunion _ -> par coq_type_ref b t;;

let coq_type_ref2 b t =
  match t with
    | Tvoid
    | Tint _
    | Tfloat _ -> coq_type_ref b t
    | Tpointer _
    | Tarray _
    | Tfunction _
    | Tcomp_ptr _
    | Tstruct _
    | Tunion _ -> par coq_type_ref b t;;

let params = coq_list (coq_pair ident coq_type_ref);;

let types b =
  bprintf b "\n(* types *)\n\n";
  TypMap.iter
    (fun t s -> bprintf b "Definition typ_%s := %a.\n\n" s coq_type t)
    !typMap;;

(*****************************************************************************)
(** expr *)

let string_of_unary_operation = function
  | Onotbool -> "!"
  | Onotint -> "~"
  | Oneg -> "-";;

let unary_operation = using string_of_unary_operation;;

let string_of_binary_operation = function
  | Oadd -> "+"
  | Osub -> "-"
  | Omul -> "*"
  | Odiv -> "/"
  | Omod -> "%"
  | Oand -> "&"
  | Oor -> "||"
  | Oxor -> "^"
  | Oshl -> "<<"
  | Oshr -> ">>"
  | Oeq -> "=="
  | One -> "!="
  | Olt -> "<"
  | Ogt -> ">"
  | Ole -> "<="
  | Oge -> ">=";;

let binary_operation = using string_of_binary_operation;;

let block = coq_Z;;

let coq_val b = function
  | Vundef -> string b "Vundef"
  | Vint x -> int b x (* thanks to Coercion Vint : int >-> expr *)
  | Vfloat x -> papp1 b "Vfloat" float x
  | Vptr (x, i) -> papp2 b "Vptr" block x int i;;

let rec exprs_of_exprlist = function
  | Enil -> []
  | Econs (e, el) -> e :: exprs_of_exprlist el;;

let string_of_incr_or_decr = function
  | Incr -> "++"
  | Decr -> "--";;

let incr_of_decr = using string_of_incr_or_decr;;

let exptypTable = ref TypMap.empty;;

let exptyp_id = ref 0;;

let int_of_exptyp t =
  try TypMap.find t !exptypTable
  with Not_found ->
    incr exptyp_id;
    exptypTable := TypMap.add t !exptyp_id !exptypTable;
    !exptyp_id;;

let expr_type b t = bprintf b "`:T%d" (int_of_exptyp t);;

let rec expr b = function
  | Eval (v, t) -> bprintf b "#%a%a" coq_val v expr_type t
  | Evar (id, t) -> bprintf b "$%a%a" ident id expr_type t
  | Efield (e, id, t) ->
      bprintf b "%a # %a%a" pexpr e ident id expr_type t
  | Evalof (Evar (id, t), _) -> bprintf b "\\%a%a" ident id expr_type t
  | Evalof (e, t) -> papp2 b "Evalof" pexpr e expr_type t
  | Ederef (e, t) -> bprintf b "`*%a%a" pexpr e expr_type t
  | Eaddrof (e, t) -> bprintf b "&%a%a" pexpr e expr_type t
  | Eunop (op, e, t) ->
      bprintf b "%a%a%a" unary_operation op pexpr e expr_type t
  | Ebinop (op, e1, e2, t) ->
      bprintf b "%a%a%a%a" pexpr e1 binary_operation op pexpr e2 expr_type t
  | Ecast (e, t) -> papp2 b "Ecast" pexpr e expr_type t
  | Econdition (e1, e2, e3, t) ->
      bprintf b "%a?%a`|%a%a" pexpr e1 pexpr e2 pexpr e3 expr_type t
  | Esizeof (t1, t2) -> papp2 b "Esizeof" expr_type t1 expr_type t2
  | Eassign (e1, e2, t) ->
      bprintf b "%a `= %a%a" pexpr e1 pexpr e2 expr_type t
  | Eassignop (op, e1, e2, t1, t2) ->
      papp5 b "Eassignop" binary_operation op pexpr e1 pexpr e2
	expr_type t1 expr_type t2
  | Epostincr (id, e, t) ->
      bprintf b "%a%a%a" pexpr e incr_of_decr id expr_type t
  | Ecomma (e1, e2, t) -> papp3 b "Ecomma" pexpr e1 pexpr e2 expr_type t
  | Ecall (e, el, t) -> papp3 b "Ecall" pexpr e exprlist el expr_type t
  | Eloc (x, i, t) -> papp3 b "Eloc" block x int i expr_type t
  | Eparen (e, t) -> papp2 b "Eparen" pexpr e expr_type t

and pexpr b = par expr b

and exprlist b el = bprintf b "E%a" (coq_list pexpr) (exprs_of_exprlist el);;

(*****************************************************************************)
(** statement *)

let label = ident;;

let rec label_stats_of_labeled_statements = function
  | LSdefault s -> [None,s]
  | LScase (i, s, ls) -> (Some i,s) :: label_stats_of_labeled_statements ls;;

let rec statement b = function
  | Sskip -> string b "Sskip"
  | Sdo e -> pexpr b e (* thanks to Coercion Sdo : expr >-> statement *)
  | Ssequence (s1, s2) -> bprintf b "%a;;\n%a" statement s1 statement s2
  | Sifthenelse (e, s1, s2) ->
      bprintf b "If %a\nthen %a\nelse %a" pexpr e statement s1 statement s2
  | Swhile (e, s) -> bprintf b "while %a do %a" pexpr e statement s
  | Sdowhile (e, s) -> bprintf b "do %a while %a" pexpr e statement s
  | Sfor (s1, e, s2, s3) -> bprintf b "for (%a, %a, %a)\n%a"
      statement s1 pexpr e statement s2 statement s3
  | Sbreak -> string b "break"
  | Scontinue -> string b "continue"
  | Sreturn oe -> papp1 b "return" (par (option pexpr)) oe
  | Sswitch (e, ls) -> papp2 b "Sswitch" pexpr e labeled_statements ls
  | Slabel (l, s) -> papp2 b "Slabel" label l statement s
  | Sgoto l -> papp1 b "goto" label l

and labeled_statements b ls =
  bprintf b "L%a" (coq_list label_stat) (label_stats_of_labeled_statements ls)

and label_stat b = function
  | None, s -> app1 b "LSdefault" statement s
  | Some i, s -> bprintf b "<%a: %a" int i statement s;;

(*****************************************************************************)
(** global variables *)

let prog_var_ref b (Coq_pair (id, _)) = bprintf b "gv_%a" ident id;;

let is_int8 = function
  | Init_int8 _ -> true
  | Init_int16 _
  | Init_int32 _
  | Init_float32 _
  | Init_float64 _
  | Init_space _
  | Init_addrof _ -> false;;

let int8 b x =
  let x = Int32.to_int (camlint_of_coqint x) in
    if x = 34 then string b ""
    else if x >= 32 && x <= 126 then bprintf b "%c" (Char.chr x)
    else bprintf b "%03d" x;;

let init_data b = function
  | Init_int8 x -> bprintf b "\"%a\"" int8 x
  | Init_int16 x -> app1 b "Init_int16" int x
  | Init_int32 x -> app1 b "Init_int32" int x
  | Init_float32 x -> app1 b "Init_float32" float32 x
  | Init_float64 x -> app1 b "Init_float64" float64 x
  | Init_space x -> app1 b "Init_space" coq_Z x
  | Init_addrof (id, x) -> app2 b "Init_addrof" ident id int x;;

let char_of_init_data = function
  | Init_int8 x ->
      let x = Int32.to_int (camlint_of_coqint x) in
	if x >= 32 && x <= 126 then Char.chr x
	else raise Not_found
  | Init_int16 _
  | Init_int32 _
  | Init_float32 _
  | Init_float64 _
  | Init_space _
  | Init_addrof _ -> raise Not_found;;

let remove_null =
  let null = Init_int8 (coqint_of_camlint 0l) in
  let rec aux x = function
    | [] -> if x = null then [] else raise Not_found
    | y :: l -> let c = char_of_init_data x in
	if c = '"' then c :: c :: aux y l else c :: aux y l
  in function
    | [] -> []
    | x :: l -> aux x l;;

let gvar_init b l =
  if List.for_all is_int8 l then
    try
      let b' = Buffer.create 100 in
	List.iter (bprintf b' "%c") (remove_null l);
	bprintf b "null_termin_string \"%a\"" Buffer.add_buffer b'
    with Not_found ->
      bprintf b "list_init_data_of_list_ascii %a%%char"
	(coq_list init_data) l
  else coq_list init_data b l;;

let prog_var_def b (Coq_pair (id, v)) =
  bprintf b "Definition gv_%a :=\n  {| gvar_info := %a;\n     \
    gvar_init := %a;\n     gvar_readonly := %a;\n     \
    gvar_volatile := %a |}.\n\n" ident id coq_type v.gvar_info
    gvar_init v.gvar_init bool v.gvar_readonly bool v.gvar_volatile;;

let global_variables b p =
  bprintf b "(* global variables *)\n\n%a\
    Definition global_variables := %a.\n"
    (list_iter prog_var_def) p.prog_vars
    (coq_list prog_var_ref) p.prog_vars;;

(*****************************************************************************)
(** functions *)

let prog_funct_ref b (Coq_pair (id, _)) = bprintf b "fun_%a" ident id;;

let coq_function b f =
  bprintf b "{| fn_return := %a;\n     fn_params := %a;\n     \
    fn_vars := %a;\n     fn_body := %a |}"
    coq_type f.fn_return params f.fn_params
    params f.fn_vars statement f.fn_body;;

let external_function b ef =
  bprintf b "{| ef_id := %a;\n     ef_sig := %a;\n     ef_inline := %a |}"
    ident ef.ef_id signature ef.ef_sig bool ef.ef_inline;;

let fundef b = function
  | Internal f -> bprintf b "Internal\n  %a" coq_function f
  | External (ef, tl, t) -> bprintf b "External\n  %a\n  %a\n  %a"
      external_function ef typelist tl pcoq_type t;;

let prog_funct_def b (Coq_pair (id, fd)) =
  bprintf b "Definition fun_%a :=\n  (%a, %a).\n\n"
    ident id ident id fundef fd;;

let functions b p =
  bprintf b "\n(* functions *)\n\n%a\n\nDefinition functions := %a.\n"
    (list_iter prog_funct_def) p.prog_funct
    (coq_list prog_funct_ref) p.prog_funct;;

(*****************************************************************************)
(** program *)

let program b p = bprintf b
  "\n(* program *)\n\nDefinition program : AST.program fundef type :=\n  \
    {| prog_funct := functions;\n    \
       prog_main := %a;\n    \
       prog_vars := global_variables |}.\n" ident p.prog_main;;

(*****************************************************************************)
(** main printing function for Csyntax.program *)

let to_buffer p =
  let b = Buffer.create 10000 and b2 = Buffer.create 10000 in
    init_identTable ();
    string b header;
    identifiers b;
    global_variables b2 p;
    functions b2 p;
    types b;
    Buffer.add_buffer b b2;
    program b p;
    b;;