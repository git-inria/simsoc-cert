(**
SimSoC-Cert, a toolkit for generating certified processor simulators
See the COPYRIGHTS and LICENSE files.

   Convert C used in the SH4 manual to pseudocode.
*)

open Shparsing.C_parse
open Shparsing.Manual
(*open Cparser*)

module C = Cabs
module E = Ast

module StringMap = Map.Make (struct type t = string let compare = compare end)

let map_affect = ref StringMap.empty 
let map_affect_spec = ref StringMap.empty 
let map_param = ref (List.fold_left (fun map k -> StringMap.add k () map) StringMap.empty [ "FPUL" ; "FPSCR" ] )

let inst_of_cabs : Cabs.definition -> E.inst option = 

  let flatten_case = (** replace the statement inside any CASE by a NOP (which location is a copy of the CASE's location) *) (* WARNING this case for example is not treated : a CASE contains a BLOCK which contains a CASE *)
    let rec aux = function
      | C.CASE (e, s, loc) :: xs -> C.CASE (e, C.NOP loc, loc) :: aux (s :: xs)
      | x :: xs -> x :: aux xs
      | [] -> [] in
    aux in

  let s_of_unary_operator = function
    | C.MINUS -> "opp" | C.PLUS -> "plus" | C.NOT -> "NOT" | C.BNOT -> "not" | C.MEMOF -> "memof" | C.ADDROF -> "addrof"
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
      | C.T_Bool -> E.Tbool
      | C.Tunsigned -> E.Tunsigned
      | C.Tunion _ -> E.Tunsigned (* FIXME floating instruction *)
      | t -> ignore t ; assert false in
    function
      | [C.SpecType o] -> t_of_typeSpecifier o
      | [C.SpecType C.Tunsigned; C.SpecType C.Tlong] -> E.Tunsigned_long
      | [C.SpecType C.Tunsigned; C.SpecType C.Tchar] -> E.Tunsigned_char
      | [C.SpecType C.Tunsigned; C.SpecType C.Tshort] -> E.Tunsigned_short
      | [C.SpecType C.Tunsigned; C.SpecType C.Tint] -> E.Tunsigned_int
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
      E.Assign (v, E.Fun (op, [v]))

    | C.COMPUTATION (C.BINARY (C.ASSIGN, v1, C.BINARY (C.ASSIGN, v2, C.BINARY (C.ASSIGN, v3, e))), _) -> 
      (* REMARK This case can be deleted and the whole expression can be treated in [e_of_expression]. 
         If we do so, we have to change the return type of [e_of_expression] to be able to get back the side affect of assigning an expression (before returning the value considered as an expression). 
         That is to modify [e_of_expression] to return a list for example. *)
      E.Block (List.rev (snd (List.fold_left 
                                (fun (e, l) v -> 
                                  let v = e_of_expression v in
                                  v, E.Assign (v, e) :: l)
                                (e_of_expression e, []) 
                                [v3; v2; v1])))

    | C.COMPUTATION (C.BINARY (op, v, e), _) -> 
      let affect_b v e f = 
        let v = e_of_expression v in
        E.Assign (v, f v (e_of_expression e)) in
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
    | C.VARIABLE ( "FPUL" | "FPSCR" | "SR" | "SSR" 
                 | "R0_BANK" | "R1_BANK" | "R2_BANK" | "R3_BANK" | "R4_BANK" | "R5_BANK" | "R6_BANK" | "R7_BANK"
                 | "TRA" | "EXPEVT"

                 | "SPC" | "GBR" | "VBR" | "SGR" | "DBR" | "MACH" | "MACL" | "PR"
                 as v) -> E.Reg (E.Var v, None)

    | C.VARIABLE "T" -> E.Range (E.CPSR, E.Flag ("T", "") (* , E.Bits ("1", "0") *) )
    | C.VARIABLE "S" -> E.Range (E.CPSR, E.Flag ("S", "") (* , E.Bits ("2", "1") *) )
    | C.VARIABLE "Q" -> E.Range (E.CPSR, E.Flag ("Q", "") (* , E.Bits ("9", "8") *) )
    | C.VARIABLE "M" -> E.Range (E.CPSR, E.Flag ("M", "") (* , E.Bits ("10", "9") *) )
    | C.VARIABLE "SR_BL" -> E.Range (E.CPSR, E.Flag ("BL", "") (* , E.Bits ("29", "28") *) )
    | C.VARIABLE "SR_RB" -> E.Range (E.CPSR, E.Flag ("RB", "") (* , E.Bits ("30", "29") *) )
    | C.VARIABLE "SR_MD" -> E.Range (E.CPSR, E.Flag ("MD", "") (* , E.Bits ("31", "30") *) )

    | C.VARIABLE i -> E.Var i

    | C.INDEX (C.VARIABLE "R", e) -> E.Reg (e_of_expression e, None)
    | C.INDEX (e1, e2) -> E.Range (e_of_expression e1, E.Index (e_of_expression e2))

    | C.PAREN e -> e_of_expression e

    | C.UNARY (op, e) -> E.Fun (s_of_unary_operator op, [ e_of_expression e ])
    | C.BINARY (op, e1, e2) -> E.BinOp (e_of_expression e1, s_of_binary_operator op, e_of_expression e2)

    | C.CONSTANT (C.CONST_INT s | C.CONST_STRING s) -> if String.length s >= 3 && s.[0] = '0' then match s.[1] with 'x' -> E.Hex s | 'b' -> E.Bin s | _ -> E.Num s else E.Num s 
    | C.CONSTANT (C.CONST_FLOAT "0.0") -> E.Float_zero

    | C.CAST ((C.SpecType C.Tunsigned :: _, C.JUSTBASE), C.SINGLE_INIT e) -> e_of_expression e
    | C.CAST (([C.SpecType (C.Tlong (*| C.Tint | C.Tshort*))], C.JUSTBASE), C.SINGLE_INIT e) -> E.Fun ("(long)", [e_of_expression e])
    | C.CAST (([C.SpecType ((*C.Tlong | *)C.Tint(* | C.Tshort*))], C.JUSTBASE), C.SINGLE_INIT e) -> E.Fun ("(int)", [e_of_expression e])
    | C.CAST (([C.SpecType ((*C.Tlong | C.Tint | *)C.Tshort)], C.JUSTBASE), C.SINGLE_INIT e) -> E.Fun ("(short)", [e_of_expression e])

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

  let add_def e =
    let rec aux acc = function
      | C.DEFINITION x :: xs -> 
        aux (match x with 
          | C.DECDEF ((l_ty, l), _) -> let ty = t_of_ltypeSpecifier l_ty in List.fold_left (fun acc ((name, _, _, _), _) -> (ty, name) :: acc) acc l 
          | t -> ignore t ; assert false) xs
      | l -> acc, l in
    let acc, l = aux [] e.C.bstmts in
    acc, { e with C.bstmts = l } in

  let i_of_definition = 
    let open Util in
    let unsupported_fundef = set_of_list
      [ (* float *)
        "check_single_exception" 
      ; "check_double_exception"
      ; "normal_faddsub"
      ; "normal_fmul" 
      ; "check_product_infinity"
      ; "check_negative_infinity"
      ; "check_positive_infinity" 
      ; "check_product_invalid"
      ; "fipr"
      ; "clear_cause" ] in

    let unsupported_decdef = set_of_list
      [ "fpu_exception_trap"
      ; "inexact"
      ; "load_int"
      ; "load_quad"
      ; "sqrt"
      ; "store_int"
      ; "store_quad"
      ; "undefined_operation"
      ; "Error"

      ; "TLB_MMUCR_URC"
      ; "frf"] in

    function
    | C.FUNDEF ((l_ty, (name, C.PROTO (_, l, _), _, _)), e, _, _) -> 
      if StrSet.mem name unsupported_fundef then
        (* FIXME float instruction is not supported *) None
      else
        let l_param = List.map (function ([C.SpecType _] as o, (n, _, _, _)) -> t_of_ltypeSpecifier o, n | t -> ignore t ; assert false) l in
        let name = (* WARNING : special keyword : the "NOT" string is sometimes translated to "not" in gencoq.ml *)
          if name = "NOT" then "NOT_" else name in
        let l_loc, e = add_def e in
        Some (E.Let ((t_of_ltypeSpecifier l_ty, name), l_param, li_of_block e, l_loc))
    | C.DECDEF ((l_ty, [((name, C.PROTO (_, [[C.SpecType C.Tvoid], _], _), _, _), _)]), _) -> 
      if StrSet.mem name unsupported_decdef then
        None
      else
      (* REMARK we choose the convention to delete the void argument (at function declaration time) instead of create a new one (at application time) *)
        let l_param = [] in 
        Some (E.Let ((t_of_ltypeSpecifier l_ty, name), l_param, [], [])) 
    | C.DECDEF ((l_ty, [((name, C.PROTO (_, l, _), _, _), _)]), _) -> 
      if StrSet.mem name unsupported_decdef then
        None
      else
      let l_param = List.map (function (l, (n, _, _, _)) -> t_of_ltypeSpecifier l, n) l in
      Some (E.Let ((t_of_ltypeSpecifier l_ty, name), l_param, [], [])) 
    | C.DECDEF ((_, l), _) -> 
      let () = 
        List.iter (function
          | ((name, C.JUSTBASE, [], _), _) when not (StrSet.mem name unsupported_decdef) ->
            map_param := StringMap.add name () !map_param
          | _ -> ()) l in
      None
    | C.ONLYTYPEDEF _ -> None
    | _ -> assert false in

  i_of_definition

let is_not_float_mmu = function
  | 34 | 44 (* floating instructions *) 
  | 53 (* mmu *) -> false 
  | _ -> true

let program_of_manual : C_parse.raw_c_code manual -> E.program = 
  fun m ->
    { E.header = List.fold_left (fun xs -> function
      | None -> xs
      | Some x -> x :: xs) []
        (List.rev_map inst_of_cabs (match C_parse.get_code m.entete with None -> assert false (* FIXME floating instruction *) | Some l -> l))

    ; E.body =
        List.fold_left (fun xs -> function
          | None -> xs
          | Some x -> x @ xs) []
      
          (List.rev_map (fun inst -> 
            match inst.decoder.dec_title with
              | Menu when is_not_float_mmu inst.position ->
                Some 
                  (List.map (function
                    | C.FUNDEF ((_, (fun_name, _, _, _)), _, _, _) as c -> 
                      
                      { E.pref = Printf.sprintf "9.%d (* %s *)" inst.position fun_name
                      ; E.pkind = E.InstARM
                      ; E.pident = { E.iname = fun_name ; E.iparams = [] ; E.ivariant = None }
                      ; E.pidents = []
                      ; E.pinst = match inst_of_cabs c with None -> assert false | Some s -> s
                      }
                
                    | _ -> assert false 
                   ) (match C_parse.get_code inst.c_code with None -> assert false | Some l -> l))

              | _ -> 
                let () = ignore ( List.map inst_of_cabs (match C_parse.get_code inst.c_code with None -> assert false | Some l -> l) ) in
            (* FIXME floating instruction *) 
                None
           ) m.section) }


let maplist_of_manual : C_parse.raw_c_code manual -> Codetype.maplist =
  fun m -> 
    List.flatten (List.map (fun i -> 
      if i.decoder.dec_title = Menu then
        let l, _ = 
          List.fold_left2 (fun (acc_l, pos) -> function (Dec_usual d, _) -> (function C.FUNDEF ((_, (fun_name, _, _, _)), _, _, _) ->  
            (Lightheadertype.LH ([9; i.position; pos], fun_name), 
             (List.fold_left (fun acc (i, nb) ->
               Array.append acc (Array.init nb (match i with 
                 | I_0 -> fun _ -> Codetype.Value false
                 | I_1 -> fun _ -> Codetype.Value true
                 | I_n -> fun i -> Codetype.Range ("n", nb, i)
                 | I_m -> fun i -> Codetype.Range ("m", nb, i)
                 | I_i -> fun i -> Codetype.Range ("i", nb, i)
                 | I_d -> fun i -> Codetype.Range ("d", nb, i)))
              ) [||] d.inst_code)) :: acc_l, succ pos | _ -> assert false) | _ -> assert false) ([], 0) i.decoder.dec_tab (match C_parse.get_code i.c_code with None -> assert false | Some l -> l) in
        List.rev l
      else
        []) m.section)
