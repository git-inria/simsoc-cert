(**
SimSoC-Cert, a toolkit for generating certified processor simulators
See the COPYRIGHTS and LICENSE files.

Convert a pseudocode AST into a Csyntax AST.
*)

open Util;;
open Ast;;
open Clight;;
open Csyntax;;
open Datatypes;;
open Printf;;


(*let input_registers = ["n"; "m"; "s"; "dLo"];;*)

let mode m = Genpc.string_of_mode m;;

let access_type = function
  | Byte -> "byte"
  | Half -> "half"
  | Word -> "word";;

(* Transformation form Pseudocode type_param to Csyntax typ*)
let rec typ_trans (t: Ast.type_param) =
  match t with
    | Ast.Tint -> Tint (I32, Signed)
    | Tlong -> Tint (I32, Signed)
    | Ast.Tfloat -> Tfloat F32
    | Tdouble -> Tfloat F64
    | Ast.Tvoid -> Tvoid
    | Tchar -> Tint (I8, Signed)
    | Tbool -> Tint (I8, Signed)
    | Tunsigned -> Tint (I32, Unsigned)
    | Tunsigned_long -> Tint (I32, Unsigned)
    | Tunsigned_char -> Tint (I8, Unsigned)
    | Tunsigned_short -> Tint (I16, Unsigned)
    | Tunsigned_int -> Tint (I32, Unsigned)
;;

(* Operations transformation, from string to Csyntax type*)
let unop_trans = function
  | "not" -> Onotbool
  | "NOT" -> Onotint
  | "-" -> Oneg
  | _ -> Oneg;;

let binop_trans = function
  | "and" -> Oand
  | "or" -> Oor
  | "AND" -> Oand
  | "OR" | "|" -> Oor
  | "EOR" -> Oxor
  | "Logical_Shift_Left" -> Oshl
  | "Logical_Shift_Right" -> Oshr
  | "==" -> Oeq
  | "!=" -> One
  | ">=" -> Oge
  | "<" -> Olt
  | "+" -> Oadd
  | "-" -> Osub
  | "<<" -> Oshl
  | "*" -> Omul
  | _ -> Oand;;

(* Number expressions, from string to Z*)
let num str = Camlcoq.z_of_camlint (Int32.of_string str);;
let bin str = Camlcoq.z_of_camlint (Int32.of_string str);;
let hex str = Camlcoq.z_of_camlint (Int32.of_string str);;

(* Transformation form Pseudocode expr to Clight expr*)
let rec exp_trans' lst = function
  | Num str -> Econst_int (num str, Tint (I32, Signed))
  | Hex str -> Econst_int (hex str, Tint (I32, Signed))
  | Bin str -> Econst_int (bin str, Tint (I32, Signed))
  | Float_zero -> Econst_float (0.0, Tfloat F32)
  | Var str -> Clight.Evar (Camlcoq.intern_string str, Tint (I8, Unsigned))
  | If_exp (e1, e2, e3) -> 
      Clight.Econdition 
        (exp_trans' lst e1,exp_trans' lst e2,exp_trans' lst e3, Tint (I8, Unsigned))
  | BinOp (e1, str, e2) -> 
      Clight.Ebinop 
        (binop_trans str, exp_trans' lst e1, exp_trans' lst e2, Tint (I32, Unsigned))
  | Fun _|CPSR|SPSR _|Range (_,Bits _)|Range (_,Flag _)|Range (_,Index _)
  | Unaffected -> Clight.Evar (Camlcoq.intern_string "unaffect", Tvoid)
  | Unpredictable_exp -> Clight.Evar (Camlcoq.intern_string "ETODO", Tvoid)
  | Memory (_, n) -> Clight.Evar (Camlcoq.intern_string ("read_"^(access_type n)), Tvoid)
  | Coproc_exp _|Reg _ -> 
      Clight.Evar (Camlcoq.intern_string "Etodo", Tvoid)
;;
(*
let id s = Camlcoq.intern_string s;;

let typeof_mmu =
  Tstruct (id "SLv6_MMU",
           Fcons (id "begin",Tint (I32,Unsigned),
           Fcons (id "size",Tint (I32,Unsigned),
           Fcons (id "end",Tint (I32,Unsigned),
           Fcons (id "mem",Tpointer (Tint (I32,Unsigned)),
           Fnil)))))
let typeof_sr = 
  Tstruct (id "SLv6_StatusRegister",
          Fcons (id "Nflag",Tint (I8,Unsigned),Fnil))
let typeof_sc =
  Tstruct (id "")
let typeof_proc =
  Tstruct (Camlcoq.intern_string "SLv6_Processor", 
           Fcons (id "mmu_ptr",Tpointer(typeof_mmu),
           Fcons (id "cpsr",typeof_sr,
           Fcons (id "spsr[5]",typeof_sr,
           Fcons (id "cp15",)))))
(* Transformation form Pseudocode expr to Csyntax expr*)
let rec exp_trans = function
  |Num str -> Eval (Values.Vint (num str),Tint (I32, Signed))
  |Hex str -> Eval (Values.Vint (hex str),Tint (I32, Signed))
  |Bin str -> Eval (Values.Vint (bin str),Tint (I32, Signed))
  |Float_zero -> Eval (Values.Vfloat 0.0,Tfloat F32)
  |Var str -> Evar (Camlcoq.intern_string str,Tint (I32, Unsigned))
  |If_exp (e1, e2, e3) -> 
     Econdition (exp_trans e1,exp_trans e2,exp_trans e3,Tint (I8, Unsigned))
  |BinOp (e1, str, e2) -> 
     Ebinop (binop_trans str, exp_trans e1, exp_trans e2,Tint (I32, Unsigned))
  |Coproc_exp _|Fun _|CPSR|SPSR _|Range (_,Bits _)|Range (_,Flag _)|Range (_,Index _)
  |Unaffected -> Ecall (Evar (Camlcoq.intern_string "ETodo", Tvoid),[],Tvoid)
  |Unpredictable_exp -> Ecall (Evar (Camlcoq.intern_string "unpredicatable",Tvoid),[],Tvoid)
  |Memory (e, n) -> 
     Evcall (Evar (Camlcoq.intern_string ("read_"^(access_type n)),Tvoid),
             exp_trans e, 
             (match n with
                |Byte->Tint (I8,Unsigned)
                |Half->Tint (I16,Unsigned)
                |Word->Tint (I32,Unsigned)))
  |Reg (e,None)->
     Ecall (Evar (Camlcoq.intern_string "reg",Tvoid),
            [Evar (Camlcoq.intern_string "proc",typeof_proc);exp_trans e],Tint (I32,Unsigned))
;;
*)
(* transformation from pseudocode instruction to clight statement*)
let rec stm_trans' lst = function
  | Block insts ->
      (match insts with
        | [] -> Clight.Sskip
        | i :: is -> Clight.Ssequence (stm_trans' lst i, stm_trans' lst (Block is)))
  | Let (_, _, insts, _) -> stm_trans' lst (Block insts)
  | Unpredictable -> Clight.Scall (None, Clight.Evar (Camlcoq.intern_string "unpredictable", Tvoid), [])

  | Affect (dst, src) -> affect lst dst src
  | Return e -> Clight.Sreturn (Some (exp_trans' lst e))
  | Case (e, s, o) ->
      Clight.Sswitch (exp_trans' lst e, switch_aux lst s o)
  | Coproc (e, f, es) -> 
      Clight.Scall (None, Clight.Evar (Camlcoq.intern_string f, Tvoid),
                    List.map (exp_trans' lst) ([e]@es))
  | For (counter, min, max, i) ->
      Clight.Ssequence (stm_trans' lst i,Clight.Sfor' 
           (Clight.Ebinop (Olt, Clight.Evar (Camlcoq.intern_string counter, Tint (I32, Unsigned)),
                           Econst_int (num max, Tint (I32, Unsigned)), Tint (I32, Unsigned)),
            Clight.Sassign (Clight.Evar (Camlcoq.intern_string counter, Tint (I32, Unsigned)),
                            Econst_int (num min, Tint (I32, Unsigned))),
            Clight.Sassign (Clight.Evar (Camlcoq.intern_string counter, Tint (I32, Unsigned)),
                            Clight.Ebinop (Oadd, Clight.Evar (Camlcoq.intern_string counter, Tint (I32, Unsigned)),
                                           Econst_int (num "1", Tint (I8, Unsigned)),
                                           Tint (I32, Unsigned)))))
  | Assert e -> Clight.Scall (None, Clight.Evar (Camlcoq.intern_string "_assert_fail", Tvoid), 
                              [exp_trans' lst e])
  | While (e, i) -> Clight.Sdowhile (exp_trans' lst e, stm_trans' lst i)
  | Proc (f, es) -> Clight.Scall (None, Clight.Evar (Camlcoq.intern_string f, Tvoid), 
                                  List.map (exp_trans' lst) es)
  | If (e, i1, i2) -> 
      Clight.Sifthenelse (exp_trans' lst e, stm_trans' lst i1, 
                          (match i2 with
                             | None -> Clight.Sskip
                             | Some i -> stm_trans' lst i ))


(*specific cases for registers and ranges assignement*)
and affect lst dst src =
  match dst with
    |Reg (Var s,None) -> 
        (match s with
           |"d" -> Clight.Scall (None, Clight.Evar (Camlcoq.intern_string "set_reg_or_pc", Tvoid),
                                [Clight.Evar (Camlcoq.intern_string "proc", Tint (I32, Unsigned));
                                 Clight.Evar (Camlcoq.intern_string "d", Tint (I32, Unsigned)); 
                                 exp_trans' lst src])
          |"15" -> Clight.Scall (None, Clight.Evar (Camlcoq.intern_string "set_pc_raw", Tvoid), 
                                 [Clight.Evar (Camlcoq.intern_string"proc", Tint (I32, Unsigned)); 
                                  exp_trans' lst src])
          |_ -> Clight.Scall (None,Clight.Evar (Camlcoq.intern_string "set_reg", Tvoid), 
                              [Clight.Evar (Camlcoq.intern_string "proc", Tint (I32, Unsigned));
                               Clight.Evar (Camlcoq.intern_string "d", Tint (I32, Unsigned)); exp_trans' lst src]))
    |Reg (Var s,Some m) ->
       Clight.Scall (None, Clight.Evar (Camlcoq.intern_string "set_reg_m",Tvoid),  
                     [Clight.Evar (Camlcoq.intern_string "proc", Tint (I32, Unsigned));
                      Clight.Evar (Camlcoq.intern_string s, Tint (I32, Unsigned)); 
                      Clight.Evar (Camlcoq.intern_string (mode m), Tint (I32, Unsigned)); 
                      exp_trans' lst src])
    |Range (e1,Index e2) ->
        Clight.Scall (None, Clight.Evar (Camlcoq.intern_string "set_bit", Tint (I32, Unsigned)), 
             [exp_trans' lst e1; exp_trans' lst e2; exp_trans' lst src])
    |Range (e,Bits (n1, n2)) ->
        Clight.Scall (None, Clight.Evar (Camlcoq.intern_string "set_bits", Tint (I32, Unsigned)), 
                      [exp_trans' lst e; Econst_int (num n1, Tint (I32, Unsigned));
                       Econst_int (num n2, Tint (I32, Unsigned)); exp_trans' lst src])
    |CPSR -> 
        (match src with
          |SPSR None -> 
            Clight.Scall (None, Clight.Evar (Camlcoq.intern_string "copy_StatusRegister", Tvoid),
                   [Clight.Efield 
                      (Clight.Eaddrof (Clight.Evar (Camlcoq.intern_string "proc", 
                                                    Tstruct (Camlcoq.intern_string "SLv6_Processor", Fnil)), 
                                       Tint (I32, Unsigned)), 
                       Camlcoq.intern_string "cpsr", Tint (I32, Unsigned));
                   Clight.Evar (Camlcoq.intern_string "spsr", 
                                Tstruct (Camlcoq.intern_string "SLv6_StatusRegister", 
                                         Fcons (Camlcoq.intern_string "proc",
                                                Tstruct (Camlcoq.intern_string "SLv6_Processor", Fnil), Fnil)))])
          |SPSR (Some m) -> 
              Clight.Scall (None, Clight.Evar (Camlcoq.intern_string "copy_StatusRegister", Tvoid),
                            [Clight.Efield 
                               (Clight.Eaddrof 
                                  (Clight.Evar (Camlcoq.intern_string "proc", Tstruct (Camlcoq.intern_string "SLv6_Processor", Fnil)), 
                                   Tint (I32, Unsigned)), Camlcoq.intern_string "cpsr", 
                                Tint (I32, Unsigned));
                             Clight.Evar (Camlcoq.intern_string "spsr_m", 
                                          Tstruct (Camlcoq.intern_string "SLv6_StatusRegister", 
                                                   Fcons (Camlcoq.intern_string "proc", 
                                                          Tstruct (Camlcoq.intern_string "SLv6_Processor", 
                                                                   Fcons (Camlcoq.intern_string (mode m), 
                                                                          Tint (I32, Unsigned), 
                                                                          Fnil)), Fnil)))])
          |(Num _|Bin _|Hex _|Float_zero|If_exp _|Fun _|BinOp _|CPSR|Reg _|Var _|Range (_,Bits _)
          |Range (_,Flag _)|Range (_,Index _)|Unaffected|Unpredictable_exp|Memory _|Coproc_exp _) as e -> 
             Clight.Scall (None, Clight.Evar (Camlcoq.intern_string "set_StatusRegister",Tvoid), 
                               [exp_trans' lst e]))
    |SPSR None ->
        (match src with
          |CPSR -> 
          Clight.Scall (None, Clight.Evar (Camlcoq.intern_string "copy_StatusRegister",Tvoid),
                        [Clight.Evar 
                           (Camlcoq.intern_string "spsr", Tstruct (Camlcoq.intern_string "SLv6_StatusRegister", 
                                                     Fcons (Camlcoq.intern_string "proc", 
                                                            Tstruct (Camlcoq.intern_string "SLv6_Processor", Fnil), 
                                                            Fnil)));
                         Clight.Efield 
                           (Clight.Eaddrof (Clight.Evar (Camlcoq.intern_string "proc", 
                                                    Tstruct (Camlcoq.intern_string "SLv6_Processor", Fnil)), 
                                            Tint (I32, Unsigned)), 
                            Camlcoq.intern_string "cpsr", Tint (I32, Unsigned))])
          |(Num _|Bin _|Hex _|Float_zero|If_exp _|Fun _|BinOp _|SPSR _|Reg _|Var _|Range (_,Bits _)
          |Range (_,Flag _)|Range (_,Index _)|Unaffected|Unpredictable_exp|Memory _|Coproc_exp _) as e -> 
              Clight.Scall (None, Clight.Evar (Camlcoq.intern_string "set_StatusRegister", Tvoid), 
                                [exp_trans' lst e]))
    |SPSR (Some m) ->
        (match src with
          |CPSR -> 
            Clight.Scall (None, Clight.Evar (Camlcoq.intern_string "copy_StatusRegister", Tvoid),
                   [Clight.Evar (Camlcoq.intern_string "spsr_m", Tstruct (Camlcoq.intern_string "SLv6_StatusRegister", 
                                           Fcons (Camlcoq.intern_string "proc", 
                                                  Tstruct (Camlcoq.intern_string "SLv6_Processor", 
                                                           Fcons (Camlcoq.intern_string (mode m), 
                                                                  Tint (I32, Unsigned), 
                                                                  Fnil)), 
                                                  Fnil)));
                    Clight.Efield (Clight.Eaddrof 
                                     (Clight.Evar (Camlcoq.intern_string "proc", 
                                                   Tstruct (Camlcoq.intern_string "SLv6_Processor", Fnil)), 
                                      Tint (I32, Unsigned)), Camlcoq.intern_string "cpsr", 
                                   Tint (I32, Unsigned))])
        |(Num _|Bin _|Hex _|Float_zero|If_exp _|Fun _|BinOp _|SPSR _|Reg _|Var _|Range (_,Bits _)
          |Range (_,Flag _)|Range (_,Index _)|Unaffected|Unpredictable_exp|Memory _|Coproc_exp _) as e -> 
            Clight.Scall (None, Clight.Evar (Camlcoq.intern_string "set_StatusRegister", Tvoid), 
                         [exp_trans' lst e]))
    |(Num _|Bin _|Hex _|Float_zero|If_exp _|Fun _|BinOp _|Reg _|Var _|Range (_,Flag _)
      |Unaffected|Unpredictable_exp|Memory _|Coproc_exp _) as e  -> 
       Sassign (exp_trans' lst dst, exp_trans' lst e)
    
and switch_aux lst s o =
  match s with
    |[] -> begin match o with
        |None -> Clight.LSdefault 
            (Clight.Scall (None, Clight.Evar (Camlcoq.intern_string "abort", Tvoid), []))
        |Some o -> Clight.LSdefault (stm_trans' lst o)
      end
    |(str, i) :: t ->
        Clight.LScase (num str, stm_trans' lst i, switch_aux lst t o)
;;

(*Global and local variables and their types of a pseudocode program *)
let type_of_var = function

  | "S" | "L" | "mmod" | "F" | "I" | "A" | "R" | "x" | "y" | "X" | "U" | "W"
  | "shifter_carry_out" | "E" -> Tint (I8, Unsigned)
      
  | "n" | "d" | "m" | "s" | "dHi" | "dLo" | "imod" | "immed_8" | "rotate_imm"
  | "field_mask" | "shift_imm" | "sat_imm" | "rotate" | "cp_num"
  | "immedH" | "immedL" | "offset_8" | "shift" 
  | "opcode_1" | "opcode_2" | "CRn" | "CRm" -> Tint (I8, Unsigned)

  | "cond" -> Tint (I32, Signed)
  | "old_mode" | "mode" -> Tint (I32, Signed)
  | "accvalue" | "result" | "value" -> Tint (I32, Unsigned)
  | _ -> Tint (I32, Unsigned)

module G = struct

  type typ = Csyntax.coq_type;;

  let global_type = type_of_var;;

  let local_type s _ = type_of_var s

  let rec explicit_annot_type ty _ = typ_trans ty
  
  let case_type = Tint (I32, Unsigned);;

end;;

module V = Ast.Make(G);;

let var_index l =
  let rec aux n = function
    | [] -> []
    | (a, b) :: t -> 
        Coq_pair (Camlcoq.intern_string a, b) 
        :: aux (n+1) t
  in aux 1 l;;

(*pseudocode instruction to clight function*)
let fn_trans p = 
  let gs, ls = V.vars p.pinst in
  let ls_id = var_index ls and gs_id = var_index gs in
  {fn_return = Tvoid;
   fn_params = gs_id;
   fn_vars = ls_id;
   Clight.fn_temps = [];
   fn_body = stm_trans' ls (p.pinst)};;

let fndef_trans p = Clight.Internal (fn_trans p);;

let fn_index p = Coq_pair (Camlcoq.intern_string p.pident.iname, fndef_trans p);;

(*pseudocode programe to clight program*)
let prog_trans ({ body = ps ; _ } : Ast.program) =
  { AST.prog_funct = List.map fn_index ps;
    AST.prog_main = Camlcoq.positive_of_camlint Int32.one;
    AST.prog_vars = []};;
