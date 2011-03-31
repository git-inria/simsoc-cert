(**
SimSoC-Cert, a toolkit for generating certified processor simulators
See the COPYRIGHTS and LICENSE files.

Convert a pseudocode AST into a Csyntax AST.
*)

open Util;;
open Ast;;
open Csyntax;;
open Datatypes;;
open Printf;;


(* specific expression of generating code *)
let mode m = Genpc.string_of_mode m;;

let input_registers = ["n"; "m"; "s"; "dLo"];;

let access_type = function
  | Byte -> "byte"
  | Half -> "half"
  | Word -> "word";;

let cpsr_flag = function
  | "31" -> "N_flag"
  | "30" -> "Z_flag"
  | "29" -> "C_flag"
  | "28" -> "V_flag"
  | "27" -> "Q_flag"
  | "24" -> "J_flag"
  | "19" -> "GE3"
  | "18" -> "GE2"
  | "17" -> "GE1"
  | "16" -> "GE0"
  | "9" -> "E_flag"
  | "8" -> "A_flag"
  | "7" -> "I_flag"
  | "6" -> "F_flag"
  | "5" -> "T_flag"
  | s -> "TODO_cpsr_flag_"^s;;

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

let id s = Camlcoq.intern_string s;;

let typeof_mmu =
  Tstruct (id "SLv6_MMU",
           Fcons (id "begin",Tint (I32,Unsigned),
           Fcons (id "size",Tint (I32,Unsigned),
           Fcons (id "end",Tint (I32,Unsigned),
           Fcons (id "mem",Tpointer (Tint (I8,Unsigned)),
           Fnil)))))
let typeof_sr = 
  Tstruct (id "SLv6_StatusRegister",
           Fcons (id "N_flag",Tint (I8,Unsigned),
           Fcons (id "Z_flag",Tint (I8,Unsigned),
           Fcons (id "C_flag",Tint (I8,Unsigned),
           Fcons (id "V_flag",Tint (I8,Unsigned),
           Fcons (id "Q_flag",Tint (I8,Unsigned),
           Fcons (id "J_flag",Tint (I8,Unsigned),
           Fcons (id "GE0",Tint (I8,Unsigned),
           Fcons (id "GE1",Tint (I8,Unsigned),
           Fcons (id "GE2",Tint (I8,Unsigned),
           Fcons (id "GE3",Tint (I8,Unsigned),
           Fcons (id "E_flag",Tint (I8,Unsigned),
           Fcons (id "A_flag",Tint (I8,Unsigned),
           Fcons (id "I_flag",Tint (I8,Unsigned),
           Fcons (id "F_flag",Tint (I8,Unsigned),
           Fcons (id "T_flag",Tint (I8,Unsigned),
           Fcons (id "mode",Tint (I32,Unsigned),
           Fcons (id "background",Tint (I32,Unsigned),
           Fnil))))))))))))))))))
let typeof_sc =
  Tstruct (id "SLv6_SystemCoproc",
           Fcons (id "ee_bit",Tint (I8,Unsigned),
           Fcons (id "u_bit",Tint (I8,Unsigned),
           Fcons (id "v_bit",Tint (I8,Unsigned),
           Fnil))))
let typeof_proc =
  Tstruct (id "SLv6_Processor", 
           Fcons (id "mmu_ptr",Tpointer (typeof_mmu),
           Fcons (id "cpsr",typeof_sr,
           Fcons (id "spsrs",Tarray (typeof_sr,num "5"),
           Fcons (id "cp15",typeof_sc,
           Fcons (id "id",Tint (I8,Unsigned),
           Fcons (id "user_regs",Tarray (Tint (I32,Unsigned),num "16"),
           Fcons (id "fiq_regs",Tarray (Tint (I32,Unsigned),num "7"),
           Fcons (id "irq_regs",Tarray (Tint (I32,Unsigned),num "2"),
           Fcons (id "svc_regs",Tarray (Tint (I32,Unsigned),num "2"),
           Fcons (id "abt_regs",Tarray (Tint (I32,Unsigned),num "2"),
           Fcons (id "und_regs",Tarray (Tint (I32,Unsigned),num "2"),
           Fcons (id "pc",Tpointer (Tint (I32,Unsigned)),
           Fnil)))))))))))));;

(* Transformation form Pseudocode expr to CompcertC expr*)

let rec exp_trans = function
  |Num str -> Eval (Values.Vint (num str),Tint (I32, Signed))
  |Hex str -> Eval (Values.Vint (hex str),Tint (I32, Signed))
  |Bin str -> Eval (Values.Vint (bin str),Tint (I32, Signed))
  |Float_zero -> Eval (Values.Vfloat 0.0,Tfloat F32)
  |Var str -> Evar (id str,type_of_var str)
  |If_exp (e1, e2, e3) -> 
     Econdition (exp_trans e1,exp_trans e2,exp_trans e3,Tint (I8, Unsigned))
  |BinOp (e1, str, e2) -> 
     Ebinop (binop_trans str, exp_trans e1, exp_trans e2,Tint (I32, Unsigned))
  |Unpredictable_exp -> 
     Ecall (Evar (id "unpredicatable",Tfunction (Tnil,Tvoid)),Enil,
            Tfunction(Tnil,Tvoid))
  |Memory (e, n) -> 
     Ecall (Evar (id ("read_"^(access_type n)),Tvoid),
             Econs (exp_trans e, Enil), 
             (match n with
                |Byte->Tint (I8,Unsigned)
                |Half->Tint (I16,Unsigned)
                |Word->Tint (I32,Unsigned)))
  |Reg (Var s,None) -> 
     if List.mem s input_registers then
       Evar (id ("old_R"^s),Tint (I32,Unsigned))
     else Ecall (Evalof (Evar (id "reg",Tfunction (Tcons (Tpointer typeof_proc,Tcons (Tint (I8,Unsigned),Tnil)),Tint (I32,Unsigned))),
                         Tfunction (Tcons (Tpointer typeof_proc,Tcons (Tint (I8,Unsigned),Tnil)),Tint (I32,Unsigned))),
            Econs (Evalof (Evar (id "proc",typeof_proc),typeof_proc), 
            Econs (Evalof (Evar (id s,Tint (I8,Unsigned)),Tint (I8,Unsigned)),
            Enil)),Tint (I32,Unsigned))
  |Reg (e,None)->
     Ecall (Evalof (Evar (id "reg",Tfunction (Tcons (Tpointer typeof_proc,Tcons (Tint (I8,Unsigned),Tnil)),Tint (I32,Unsigned))),
                          Tfunction (Tcons (Tpointer typeof_proc,Tcons (Tint (I8,Unsigned),Tnil)),Tint (I32,Unsigned))),
            Econs (Evalof (Evar (id "proc",typeof_proc),typeof_proc), 
            Econs (Evalof (exp_trans e,typeof (exp_trans e)), Enil)),Tint (I32,Unsigned))
  |Reg (e,Some m) ->
     Ecall (Evalof (Evar (id "reg_m",Tfunction (Tcons (Tpointer typeof_proc,Tcons (Tint (I8,Unsigned),Tcons (Tint (I8,Unsigned),Tnil))),Tint (I32,Unsigned))),
                    ),
            Econs (Evalof (Evar (id "proc",typeof_proc),typeof_proc), 
            Econs (Evalof (exp_trans e,typeof (exp_trans e)),
            Econs (Evalof (Evar (id (mode m),Tint (I32,Unsigned)),Tint (I32,Unsigned)),
            Enil))),Tint (I32,Unsigned))
  |Coproc_exp (e,f,es) ->Ecall (Evalof (Evar (id f, Tint (I32,Unsigned)),Tint (I32,Unsigned)),
                                Econs (Evalof (exp_trans e,typeof (exp_trans e)),
                                explst es),typeof (exp_trans e))
  |Fun (f,es)->
     Ecall (Evalof (Evar (id f,implicit_type f),(implicit_type f)),(implicit_arg es f),(implicit_type f))
  |CPSR->
     Ecall (Evar (id "StatusRegister_to_uint32",Tint (I32,Unsigned)),
            Econs (Eaddrof (Efield (Evar (id "proc",typeof_proc),id "cpsr",typeof_sr),typeof_sr),Enil),Tint (I32,Unsigned))
  |SPSR None ->
     Ecall (Evar (id "StatusRegister_to_uint32",Tint (I32,Unsigned)),
            Econs (Ecall (Evar (id "spsr",typeof_sr),
                          Econs (Evar (id "proc",typeof_proc),Enil),Tint (I32,Unsigned)),Enil),Tint (I32,Unsigned))
  |SPSR (Some m)->
     Ecall (Evar (id "StatusRegister_to_uint32",Tint (I32,Unsigned)),
            Econs (Ecall (Evar (id "spsr_m",typeof_sr),
                          Econs (Evar (id "proc",typeof_proc),
                          Econs (Evar (id (mode m),typeof_proc),Enil)),Tint (I32,Unsigned)),Enil),Tint (I32,Unsigned))
  |Range (e,Bits (n1,n2))->
     Ecall (Evar (id "get_bits",Tint (I32,Signed)),
            Econs (exp_trans e,
            Econs (Eval (Values.Vint (num n1),Tint (I32,Unsigned)),
            Econs (Eval (Values.Vint (num n2),Tint (I32,Unsigned)),Enil))),Tint (I32,Unsigned))
  |Range (_,Flag (s,_))-> (*"proc->cpsr.%s_flag"*)
     Efield (Efield (Evar (id "proc",typeof_proc),id "cpsr",typeof_sr),id (s^"_flag"), Tint (I8,Unsigned))
  |Range (CPSR,Index (Num n)) -> (*"proc->cpsr.%s"*)
     Efield (Efield (Evar (id "proc",typeof_proc),id "cpsr",typeof_sr),id (cpsr_flag n), Tint (I8,Unsigned))
  |Range (e1,Index e2) ->
     Ecall (Evar (id "get_bit",Tint (I32,Signed)),
            Econs (exp_trans e1,Econs (exp_trans e2,Enil)),Tint (I32,Unsigned))
  |Unaffected -> Ecall (Evar (id "ETodo", Tvoid),Enil,Tvoid)

and explst = function
  |[] -> Enil
  |h::t -> Econs (Evalof (exp_trans h,typeof (exp_trans h)),explst t)

and implicit_arg es = function
  |"ConditionPassed" ->
     Econs (Eaddrof (Efield (Evar (id "proc",typeof_proc),id "cpsr",typeof_sr),typeof_sr),explst es)
  |"write_word" | "write_half" | "write_byte" ->
     Econs (Efield (Evar (id "proc",typeof_proc),id "mmu_ptr",typeof_mmu),explst es)
  |"CP15_reg1_EEbit" | "CP15_reg1_Ubit" | "CP15_reg1_Vbit" -> 
     Econs (Eaddrof (Efield (Evar (id "proc",typeof_proc),id "cp15",typeof_sc),typeof_sc),explst es)
  |"InAPrivilegedMode"|"CurrentModeHasSPSR"|"address_of_next_instruction"
  |"address_of_current_instruction"|"high_vectors_configured"|"set_reg_m" ->
     Econs (Evar (id "proc", typeof_proc),explst es)
  | _ -> explst es

and implicit_type = function
  |"ConditionPassed" -> 
     Tfunction (Tcons (Tpointer typeof_proc,Tcons (Tint (I32,Unsigned),Tnil)),Tint (I8,Unsigned))
  |_ -> Tvoid
;;

(* transformation from pseudocode instruction to CompcertC statement*)
let rec stm_trans = function
  |Block insts ->
      (match insts with
        |[] -> Csyntax.Sskip
        |i::is -> Csyntax.Ssequence (stm_trans i, stm_trans (Block is)))
  |Let (_, _, insts, _) -> stm_trans (Block insts)
  |Unpredictable -> Sdo (Ecall (Evar (id "unpredictable", Tvoid),Enil,Tvoid))
  |Affect (dst, src) -> affect dst src
  |Return e -> Sreturn (Some (exp_trans e))
  |Case (e,s,o) ->
     Csyntax.Sswitch (exp_trans e, switch_aux s o)
  |Coproc (e, f, es) -> 
     Csyntax.Sdo (Ecall (Evar (id f, Tvoid),explst ([e]@es), Tvoid))
  |For (counter,min,max,i) ->
     Csyntax.Sfor (Sdo (Eassign (Evar (id counter,Tint (I32,Unsigned)),
                                 (Eval (Values.Vint (num min),Tint (I32,Unsigned))),Tint (I32,Unsigned))),
                   Ebinop (Olt,Evar (id counter,Tint (I32,Unsigned)),Eval (Values.Vint (num max),Tint (I32,Unsigned)),Tint (I32,Unsigned)),
                   Sdo (Epostincr (Incr,Evar (id counter,Tint (I32,Unsigned)),Tint (I32,Unsigned))),
                   stm_trans i)
  |Assert e -> Sdo (Ecall (Evar (id "_assert_fail", Tvoid),explst [e],Tvoid))
  |While (e,i) -> Csyntax.Sdowhile (exp_trans e,stm_trans i)
  |Proc (f,es) -> Sdo (Ecall (Evar (id f,Tvoid),explst es,Tvoid))
  |If (e,i1,i2) -> Csyntax.Sifthenelse (exp_trans e,stm_trans i1, 
                                        (match i2 with
                                           | None -> Csyntax.Sskip
                                           | Some i -> stm_trans i ))

(*specific cases for registers and ranges assignement*)
and affect dst src =
  match dst with
    |Reg (Var s,None) -> 
        (match s with
           |"d"-> Sdo (Ecall (Evar (id "set_reg_or_pc",Tvoid),
                               Econs (Evar (id "proc",typeof_proc),
                               Econs (Evar (id "d",Tint (I8,Unsigned)),
                               Econs (exp_trans src,Enil))),Tvoid))
           |"15"-> Sdo (Ecall (Evar (id "set_pc_raw", Tvoid), 
                               Econs (Evar (id "proc",typeof_proc),Enil),Tvoid))
           |s -> Sdo (Ecall (Evar (id "set_reg",Tvoid),
                             Econs (Evar (id "proc",typeof_proc),
                             Econs (Evar (id s,Tint (I8,Unsigned)),
                             Econs (exp_trans src,Enil))),Tvoid)))
    |Reg (Var s,Some m) -> Sdo (Ecall (Evar (id "set_reg_m",Tvoid),  
                                       Econs (Evar (id "proc",typeof_proc),
                                       Econs (Evar (id s,Tint (I8,Unsigned)),
                                       Econs (Evar (id (mode m),Tint (I32, Unsigned)),
                                       Econs (exp_trans src,Enil)))),Tvoid))
    |Range (e1,Index e2) ->
        Sdo (Ecall (Evar (id "set_bit", Tint (I32, Unsigned)), 
             Econs (exp_trans e1, Econs (exp_trans e2,Econs (exp_trans src, Enil))),Tvoid))
    |Range (e,Bits (n1, n2)) ->
        Sdo (Ecall (Evar (id "set_field",Tint (I32, Unsigned)), 
                    Econs (exp_trans e,
                    Econs (Eval (Values.Vint (num n1),Tint (I32,Unsigned)),
                    Econs (Eval (Values.Vint (num n2),Tint (I32,Unsigned)),Enil))),Tvoid))
    |CPSR -> 
        (match src with
          |SPSR None -> (*"copy_StatusRegister(&proc->cpsr, spsr(proc))"*)
             Sdo (Ecall (Evar (id "copy_StatusRegister", Tvoid),
                  Econs (Efield (Eaddrof (Evar (id "proc", typeof_proc),Tint (I32,Unsigned)),id "cpsr",typeof_sr),
                  Econs (Ecall (Evar (id "spsr",typeof_sr),Econs (Evar (id "proc",typeof_proc),Enil),typeof_sr),
                  Enil)),Tvoid))
          |SPSR (Some m) -> (*"copy_StatusRegister(&proc->cpsr, spsr_m(proc,m))"*)
             Sdo (Ecall (Evar (id "copy_StatusRegister", Tvoid),
                  Econs (Efield (Eaddrof (Evar (id "proc", typeof_proc),Tint (I32,Unsigned)),id "cpsr",typeof_sr),
                  Econs (Ecall (Evar (id "spsr_m",typeof_sr),
                                Econs (Evar (id "proc",typeof_proc),
                                Econs (Evar (id (mode m),Tint (I32,Unsigned)),Enil)),typeof_sr),
                  Enil)),Tvoid))
          |(Num _|Bin _|Hex _|Float_zero|If_exp _|Fun _|BinOp _|CPSR|Reg _|Var _|Range (_,Bits _)
          |Range (_,Flag _)|Range (_,Index _)|Unaffected|Unpredictable_exp|Memory _|Coproc_exp _) as e -> 
             Sdo (Ecall (Evar (id "set_StatusRegister",Tvoid),Econs (exp_trans e,Enil),Tvoid)))
    |SPSR None ->
        (match src with
          |CPSR -> (*"copy_StatusRegister(spsr(proc), &proc->cpsr)"*)
             Sdo (Ecall (Evar (id "copy_StatusRegister",Tvoid),
                         Econs (Ecall (Evar (id "spsr",typeof_sr),Econs (Evar (id "proc",typeof_proc),Enil),Tvoid),
                         Econs (Efield (Eaddrof (Evar (id "proc", typeof_proc),Tint (I32,Unsigned)),id "cpsr",typeof_sr),
                         Econs (Ecall (Evar (id "spsr",typeof_sr),Econs (Evar (id "proc",typeof_proc),Enil),typeof_sr),
                         Enil))),Tvoid))
          |(Num _|Bin _|Hex _|Float_zero|If_exp _|Fun _|BinOp _|SPSR _|Reg _|Var _|Range (_,Bits _)
          |Range (_,Flag _)|Range (_,Index _)|Unaffected|Unpredictable_exp|Memory _|Coproc_exp _) as e -> 
             Sdo (Ecall (Evar (id "set_StatusRegister", Tvoid),Econs (exp_trans e,Enil),Tvoid)))
    |SPSR (Some m) ->
        (match src with
          |CPSR -> (*"copy_StatusRegister(spsr_m(proc,m), &proc->cpsr)"*)
             Sdo (Ecall (Evar (id "copy_StatusRegister", Tvoid),
                         Econs (Ecall (Evar (id "spsr_m",typeof_sr),
                                       Econs (Evar (id "proc",typeof_proc),
                                       Econs (Evar (id (mode m),Tint (I32,Unsigned)),Enil)),Tvoid),
                         Econs (Efield (Eaddrof (Evar (id "proc", typeof_proc),Tint (I32,Unsigned)),id "cpsr",typeof_sr),
                         Econs (Ecall (Evar (id "spsr",typeof_sr),Econs (Evar (id "proc",typeof_proc),Enil),typeof_sr),
                         Enil))),Tvoid))
          |(Num _|Bin _|Hex _|Float_zero|If_exp _|Fun _|BinOp _|SPSR _|Reg _|Var _|Range (_,Bits _)
          |Range (_,Flag _)|Range (_,Index _)|Unaffected|Unpredictable_exp|Memory _|Coproc_exp _) as e -> 
             Sdo (Ecall (Evar (id "set_StatusRegister",Tvoid),Econs (exp_trans e,Enil),Tvoid)))
    |Num _|Bin _|Hex _|Float_zero|If_exp _|Fun _|BinOp _|Reg _|Var _|Range (_,Flag _)
    |Unaffected|Unpredictable_exp|Memory _|Coproc_exp _  -> 
       Sdo (Eassign (exp_trans dst,exp_trans src,Tvoid))

and switch_aux s o =
  match s with
    |[] -> (match o with
              |None -> LSdefault 
                 (Sdo (Ecall (Evar (id "abort", Tvoid), Enil, Tvoid)))
              |Some o -> LSdefault (stm_trans o))
    |(str, i) :: t ->
        LScase (num str, stm_trans i, switch_aux t o)

and explst = function
  |[] -> Enil
  |h::t -> Econs (exp_trans h,explst t)
;;

let var_id l =
  let rec aux = function
    | [] -> []
    | (a, b) :: t -> 
        Coq_pair (id a, b) 
        :: aux t
  in aux l;;

(*declaration for loading old_R *)
let rec oldr_decl rs st =
  let aux r =
  Sdo (Eassign (Evar (id ("old_R"^r),Tint (I32,Unsigned)),
                Ecall (Evar (id "reg",Tint (I32,Unsigned)),
                       Econs (Evar (id "proc",typeof_proc), 
                       Econs (Evar (id r,Tint (I32,Unsigned)), Enil)),
                       Tint (I32,Unsigned)),Tint(I32,Unsigned)))
  in match rs with
    | [] -> st
    | r::rs -> Ssequence (aux r, oldr_decl rs st)
;;

(*pseudocode instruction to clight function*)
let fn_trans p = 
  let gs, ls = V.vars p.pinst in
  let ls_id = var_id ls in
  let gs_id = var_id gs in
  let ss = List.fold_left (fun l (s, _) -> s::l) [] gs in
  let old_r =  List.filter (fun x -> List.mem x input_registers) ss in
  let fvar = 
    (List.map (fun x->Coq_pair (id ("old_R"^x),Tint (I32,Unsigned))) old_r)@ls_id in
  {fn_return = Tvoid;
   fn_params = (Coq_pair (id "proc",Tpointer (typeof_proc)))::gs_id;
   fn_vars = fvar;
   fn_body = oldr_decl old_r (stm_trans (p.pinst))};;

let fndef_trans p = Internal (fn_trans p);;

let fn_index p = Coq_pair (id p.pident.iname, fndef_trans p);;

(*pseudocode programe to clight program*)
let prog_trans ({ body = ps ; _ } : Ast.program) =
  { AST.prog_funct = List.map fn_index ps;
    AST.prog_main = id "main";
    AST.prog_vars = []};;

let print_cc ps = RawCoq_Csyntax_main.to_buffer (prog_trans ps)
