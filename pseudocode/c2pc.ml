module States = struct
  type t = 
    | Tiret
    | Pos of int
    | Range of int * int
end

module T_bit = struct
  type t = 
    | Tiret
    | Zero
    | One
    | One_Zero
    | Borrow
    | Carry
    | LSB
    | MSB
    | Overflow
    | Result_of_
    | Test
    | Underflow
    | Empty
end

type inst_code = 
  | I_0
  | I_1
  | I_n
  | I_m
  | I_i
  | I_d

type decoder_line = 
    { before_code : string
    ; inst_code : (inst_code * int) list
    ; states : States.t
    ; t_bit : T_bit.t } 

type decoder_rep = 
  | Dec_usual of decoder_line
  | Dec_dash of bool option

type dec_title = (** For the following cases, the words after "Menu" is the words we have to append (in front of the usual "Format, Summary of Operation, Instruction Code, Execution States, T Bit") to get the real title *)
  | Menu (* [ "Format" ; "Summary of Operation" ; "Instruction Code" ; "Execution States" ; "T Bit" ] *)

  (** 9.25 include to 9.47 include, 9.34 9.44 are exceptions *)
  | Menu_PR
  | Menu_NO_PR
  | Menu_NO_SZ

type decoder = 
    { dec_tab : (decoder_rep * string list) list (** *)
    ; dec_inst_ty : string
    ; dec_title : dec_title
    ; dec_title_long : string
    ; dec_other : string * string * string list }

type raw_c_code = 
    { init : string list (* WARNING [init] is unused *)
    ; code : Cabs.definition list (** representation of the C pseudocode, natural order : first element in the list = first line *) }

type 'a instruction = 
    { explanation_desc : string list (** information present in the part "description" *) 
    ; explanation_other : string list (** information eventually present after the C code *)


    ; decoder : decoder
    ; c_code : 'a
    ; position : int }

type 'a manual = 
    { entete : 'a (** piece of C code present at the beginning of section 9 *) 
    ; section : 'a instruction list }


module Traduction =
struct

  module C = Cabs
  module E = Ast

  module StringMap = Map.Make (struct type t = string let compare = compare end)

  let map_affect = ref StringMap.empty 
  let map_affect_spec = ref StringMap.empty 
  let map_param = ref StringMap.empty

let inst_of_cabs : Cabs.definition -> (((E.type_param * string) list -> E.inst) -> E.inst) option = 

  let flatten_case = (** replace the statement inside any CASE by a NOP (which location is a copy of the CASE's location) *) (* WARNING this case for example is not treated : a CASE contains a BLOCK which contains a CASE *)
    let rec aux = function
      | C.CASE (e, s, loc) :: xs -> C.CASE (e, C.NOP loc, loc) :: aux (s :: xs)
      | x :: xs -> x :: aux xs
      | [] -> [] in
    aux in

  let s_of_unary_operator = function
    | C.MINUS -> "minus" | C.PLUS -> "plus" | C.NOT -> "NOT" | C.BNOT -> "not" | C.MEMOF -> "memof" | C.ADDROF -> "addrof"
   (*| PREINCR | PREDECR*) | C.POSINCR -> "succ" | C.POSDECR -> "pred" | _ -> assert false in

  let s_of_binary_operator = function
    | C.ADD -> "+" | C.SUB -> "-" | C.MUL -> "*" | C.DIV -> "divu" (* MOD *) 
    | C.AND -> "and" | C.OR -> "or"
    | C.BAND -> "AND" | C.BOR -> "OR" | C.XOR -> "EOR" | C.SHL -> "Logical_Shift_Left" | C.SHR -> "Logical_Shift_Right" 
    | C.EQ -> "==" | C.NE -> "!=" | C.LT -> "<" | C.GT -> "zgt" | (* LE *) C.GE -> ">="
    (*| ASSIGN
    | ADD_ASSIGN | SUB_ASSIGN | MUL_ASSIGN | DIV_ASSIGN | MOD_ASSIGN
    | BAND_ASSIGN | BOR_ASSIGN | XOR_ASSIGN | SHL_ASSIGN | SHR_ASSIGN*) | _ -> assert false in

  let simple_binary_operator = function
    | C.ADD_ASSIGN -> C.ADD | C.SUB_ASSIGN -> C.SUB | C.MUL_ASSIGN -> C.MUL | C.DIV_ASSIGN -> C.DIV (* MOD *)
    | C.BAND_ASSIGN -> C.BAND | C.BOR_ASSIGN -> C.BOR | C.XOR_ASSIGN -> C.XOR | C.SHL_ASSIGN -> C.SHL | C.SHR_ASSIGN -> C.SHR | _ -> assert false in

  let t_of_ltypeSpecifier = 
    let t_of_typeSpecifier = function
      | C.Tint  -> E.Tint 
      | C.Tlong  -> E.Tlong 
      | C.Tfloat  -> E.Tfloat 
      | C.Tdouble -> E.Tdouble
      | C.Tvoid -> E.Tvoid 
      | C.Tchar -> E.Tchar
      | t -> ignore t ; assert false in
    function
      | [C.SpecType o] -> t_of_typeSpecifier o
      | [C.SpecType C.Tunsigned; C.SpecType C.Tlong] -> E.Tunsigned_long
      | [C.SpecType C.Tunsigned; C.SpecType C.Tchar] -> E.Tunsigned_char
      | [C.SpecType C.Tunsigned; C.SpecType C.Tshort] -> E.Tunsigned_short
      | t -> ignore t ; assert false in


  let rec li_of_block { C.bstmts = l ; _ } =
    List.map i_of_statement (List.rev (List.fold_left (fun xs -> function C.NOP _ -> xs | x -> x :: xs) [] l))
      
  and i_of_statement = function 
    | C.IF (e, s1, C.NOP _, _) -> E.If (e_of_expression e, i_of_statement s1, None)
    | C.IF (e, C.NOP _, s2, _) -> E.If (e_of_expression e, E.Block [], Some (i_of_statement s2))
    | C.IF (e, s1, s2, _) -> E.If (e_of_expression e, i_of_statement s1, Some (i_of_statement s2))

    | C.NOP _ -> assert false

    | C.COMPUTATION (C.UNARY (C.POSINCR | C.POSDECR as op, v), _) -> 
      let v, op = e_of_expression v, s_of_unary_operator op in
      E.Affect (v, E.Fun (op, [v]))

    | C.COMPUTATION (C.BINARY (C.ASSIGN, v1, C.BINARY (C.ASSIGN, v2, C.BINARY (C.ASSIGN, v3, e))), _) -> 
      (* REMARK This case can be deleted and the whole expression can be treated in [e_of_expression]. 
         If we do so, we have to change the return type of [e_of_expression] to be able to get back the side affect of assigning an expression (before returning the value considered as an expression). 
         That is to modify [e_of_expression] to return a list for example. *)
      E.Block (List.rev (snd (List.fold_left 
                                (fun (e, l) v -> 
                                  let v = e_of_expression v in
                                  v, E.Affect (v, e) :: l)
                                (e_of_expression e, []) 
                                [v3; v2; v1])))

    | C.COMPUTATION (C.BINARY (op, v, e), _) -> 
      let affect_b v e f = 
        let v = e_of_expression v in
        E.Affect (v, f v (e_of_expression e)) in
      if op = C.ASSIGN then
        affect_b v e (fun _ e -> e)
      else
        affect_b v e (fun v e -> E.BinOp (v, s_of_binary_operator (simple_binary_operator op), e))

    | C.COMPUTATION (C.CALL (C.VARIABLE s, l), _) -> E.Proc (s, List.map e_of_expression l)

    | C.DEFINITION _ -> E.Block []
    (*| i -> ignore i ; assert false*)

    | C.BLOCK (b, _) -> E.Block (li_of_block b)
    | C.SWITCH (e, C.BLOCK ({ C.bstmts = l ; _ }, _), _) -> 

      let _, acc, def = (* WARNING we evaluate [i_of_statement] from the end of the list as at the time of writing, this function is pure *)

        let verify_break = (** verify that there is no instructions after every BREAK (CASE and DEFAULT are the only allowed) *)
          let rec aux = function
            | C.BREAK _ :: xs -> 
              let () = match xs with [] | C.CASE _ :: _ | C.DEFAULT _ :: _ -> () | _ -> assert false in
              aux xs
            | _ :: xs -> aux xs
            | [] -> () in
          aux in
        let () = verify_break l in

        let mk_inst x = E.Block x in

        List.fold_right 
          (fun s (acc_c, acc, def) -> 
            let f_acc_c s = i_of_statement s :: acc_c in
            match s with 
              | C.CASE (e, _, _) -> 
                
                acc_c, ((match e with 
                  | C.CONSTANT (C.CONST_INT i) -> i
                  | C.VARIABLE v -> ignore v ; "" (* FIXME récupérer la valeur entière associé à [v] *)
                  | _ -> assert false), mk_inst acc_c) :: acc, def

              | C.BREAK _ -> [], acc, def
              | C.DEFAULT (nop, _) when (match nop with C.NOP _ -> true | _ -> assert false) -> 
                if (def, acc) = (None, []) then
                  acc_c, [], Some (mk_inst acc_c) 
                else
                  assert false (* test : presence of "default" at the end of the "switch" only *)
              | x -> f_acc_c x, acc, def
          ) (flatten_case l) ([], [], None) in
      E.Case (e_of_expression e, acc, def)

    | C.RETURN (e, _) -> E.Return (e_of_expression e)

    | C.FOR (C.FC_EXP (C.BINARY (C.ASSIGN, C.VARIABLE i, C.CONSTANT (C.CONST_INT i_deb))), 
             C.BINARY (C.LT, C.VARIABLE i_, C.CONSTANT (C.CONST_INT i_end)),
             C.UNARY (C.POSINCR, C.VARIABLE i__),
             st,
             _) when List.for_all ((=) i) [ i_ ; i__ ] -> E.For (i, i_deb, i_end, i_of_statement st)

    | i -> ignore i ; assert false

  and e_of_expression = function
    | C.VARIABLE "PC" -> E.Reg (E.Num "15", None)
    | C.VARIABLE i -> E.Var i

    | C.INDEX (C.VARIABLE "R", e) -> E.Reg (e_of_expression e, None)
    | C.INDEX (e1, e2) -> E.Range (e_of_expression e1, E.Index (e_of_expression e2))

    | C.PAREN e -> e_of_expression e

    | C.UNARY (op, e) -> E.Fun (s_of_unary_operator op, [ e_of_expression e ])
    | C.BINARY (op, e1, e2) -> E.BinOp (e_of_expression e1, s_of_binary_operator op, e_of_expression e2)

    | C.CONSTANT (C.CONST_INT s) -> if String.length s >= 3 && s.[0] = '0' then match s.[1] with 'x' -> E.Hex s | 'b' -> E.Bin s | _ -> E.Num s else E.Num s 
    | C.CONSTANT (C.CONST_FLOAT "0.0") -> E.Float_zero

    | C.CAST (_, C.SINGLE_INIT e) -> e_of_expression e

    | C.CALL (C.VARIABLE s, l) -> E.Fun (s, List.map e_of_expression l)

    | C.MEMBEROF
        (C.PAREN
           (C.UNARY (C.MEMOF,
                     C.CAST
                       (([C.SpecType (C.Tstruct ("SR0", None, []))], C.PTR ([], C.JUSTBASE)),
                        C.SINGLE_INIT (C.PAREN (C.UNARY (C.ADDROF, C.VARIABLE "SR")))))) as e,
         s) -> 
      let () = map_affect_spec := StringMap.add s () !map_affect_spec in
      E.Fun (Printf.sprintf "__get_special_%s" s, [ e_of_expression e ])
    | C.MEMBEROF (C.VARIABLE _ | C.INDEX (C.VARIABLE _, (C.VARIABLE _ | C.CONSTANT (C.CONST_INT _))) as e, s) -> 
      let () = map_affect := StringMap.add s () !map_affect in
      E.Fun (Printf.sprintf "__get_%s" s, [ e_of_expression e ]) (*E.Member_of (e_of_expression e, s) *)

    | e -> ignore e ; assert false

  in

  let i_of_definition = 
    let open Util in
    let unsupported_fun = set_of_list
      [ "check_single_exception" 
      ; "check_double_exception"
      ; "normal_faddsub"
      ; "normal_fmul" 
      ; "check_product_infinity"
      ; "check_negative_infinity"
      ; "check_positive_infinity" 
      ; "check_product_invalid"
      ; "fipr"
      ; "clear_cause" ] in
    function
    | C.FUNDEF ((l_ty, (name, C.PROTO (_, l, _), _, _)), e, _, _) -> 
      if StrSet.mem name unsupported_fun then
	(* FIXME float instruction is not supported *) None
      else
	let l_param = List.map (function ([C.SpecType _] as o, (n, _, _, _)) -> t_of_ltypeSpecifier o, n | t -> ignore t ; assert false) l in
	Some (fun i -> 
          E.Let ((t_of_ltypeSpecifier l_ty, name), l_param, li_of_block e, i l_param))
    | C.DECDEF ((l_ty, [((name, C.PROTO (_, [[C.SpecType C.Tvoid], _], _), _, _), _)]), _) -> 
      (* REMARK we choose the convention to delete the void argument (at function declaration time) instead of create a new one (at application time) *)
      let l_param = [] in 
      Some (fun i -> 
        E.Let ((t_of_ltypeSpecifier l_ty, name), l_param, [], i l_param)) 
    | C.DECDEF ((l_ty, [((name, C.PROTO (_, l, _), _, _), _)]), _) -> 
      let l_param = List.map (function (l, (n, _, _, _)) -> t_of_ltypeSpecifier l, n) l in
      Some (fun i -> 
        E.Let ((t_of_ltypeSpecifier l_ty, name), l_param, [], i l_param)) 
    | C.DECDEF ((_, [((name, C.JUSTBASE, [], _), _)]), _) -> 
      let () = map_param := StringMap.add name () !map_param in
      None
    | C.DECDEF _
    | C.ONLYTYPEDEF _ -> None
    | _ -> assert false in

  i_of_definition



let prog_list_of_manual : raw_c_code manual -> E.program = 
  fun m ->
    { E.header = List.fold_left (fun xs -> function
      | None -> xs
      | Some x -> x :: xs) []
        
        (List.rev_map (fun c ->
          match inst_of_cabs c with
            | None -> None
            | Some f -> Some (f (fun _ -> E.Block []))) m.entete.code)

    ; E.body =
        List.fold_left (fun xs -> function
          | None -> xs
          | Some x -> x @ xs) []
      
          (List.rev_map (fun inst -> 
            match inst.decoder.dec_title with
              | Menu ->
                Some 
                  (List.map (function
                    | C.FUNDEF ((_, (fun_name, _, _, _)), _, _, _) as c -> 
                      
                      { E.pref = Printf.sprintf "9.%d (* %s *)" inst.position fun_name
                      ; E.pkind = E.InstARM
                      ; E.pident = { E.iname = fun_name ; E.iparams = [] ; E.ivariant = None }
                      ; E.pidents = []
                      ; E.pinst = 
                          let code = match inst_of_cabs c with None -> assert false | Some s -> s in
                          code (fun l -> E.Proc (fun_name, List.map (fun (_, x) -> E.Var x) l)) }
                
                    | _ -> assert false 
                   ) inst.c_code.code)
              | _ -> 
                let () = ignore ( List.map inst_of_cabs inst.c_code.code ) in
            (* FIXME prise en charge des flottants *) 
                None
           ) m.section) }

end
