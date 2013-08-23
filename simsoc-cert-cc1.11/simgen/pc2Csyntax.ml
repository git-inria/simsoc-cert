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
open Fappli_IEEE;;


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
    | Ast.Tint -> Tint (I32, Signed, noattr)
    | Tlong -> Tint (I32, Signed, noattr)
    | Ast.Tfloat -> Tfloat (F32, noattr)
    | Tdouble -> Tfloat (F64, noattr)
    | Ast.Tvoid -> Tvoid
    | Tchar -> Tint (I8, Signed, noattr)
    | Tbool -> Tint (I8, Signed, noattr)
    | Tunsigned -> Tint (I32, Unsigned, noattr)
    | Tunsigned_long -> Tint (I32, Unsigned, noattr)
    | Tunsigned_char -> Tint (I8, Unsigned, noattr)
    | Tunsigned_short -> Tint (I16, Unsigned, noattr)
    | Tunsigned_int -> Tint (I32, Unsigned, noattr)
;;


(*Global and local variables and their types of a pseudocode program *)
let type_of_var = function

  | "S" | "L" | "mmod" | "F" | "I" | "A" | "R" | "x" | "y" | "X" | "U" | "W"
  | "shifter_carry_out" | "E" -> Tint (I8, Signed, noattr)
      
  | "n" | "d" | "m" | "s" | "dHi" | "dLo" | "imod" | "immed_8" | "rotate_imm"
  | "field_mask" | "shift_imm" | "sat_imm" | "rotate" | "cp_num"
  | "immedH" | "immedL" | "offset_8" | "shift" 
  | "opcode_1" | "opcode_2" | "CRn" | "CRm" -> Tint (I8, Unsigned, noattr)

  | "cond" -> Tint (I32, Signed, noattr)
  | "old_mode" | "mode" -> Tint (I32, Signed, noattr)
  | "accvalue" | "result" | "value" -> Tint (I32, Unsigned, noattr)
  | _ -> Tint (I32, Unsigned, noattr)

module G = struct

  type typ = Csyntax.coq_type;;

  let global_type = type_of_var;;

  let local_type s _ = type_of_var s

  let rec explicit_annot_type ty _ = typ_trans ty
  
  let case_type = Tint (I32, Unsigned, noattr);;

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

(* Notations for long type definition *)
let uint32 = Tint (I32,Unsigned, noattr);;
let int32 = Tint (I32,Signed, noattr);;
let uint8 = Tint (I8,Unsigned, noattr);;
let int8 = Tint (I8,Signed, noattr);;
(* Type representation of struct SLv6_MMU *)
let tp_mmu =
  Tstruct (id "SLv6_MMU",
           Fcons (id "begin",uint32,
           Fcons (id "size",uint32,
           Fcons (id "end",uint32,
           Fcons (id "mem",Tpointer (uint8, noattr),
           Fnil)))), noattr)

(* Type representation of struct SLv6_StatusRegister *)
let tp_sr = 
  Tstruct (id "SLv6_StatusRegister",
           Fcons (id "N_flag",uint8,
           Fcons (id "Z_flag",uint8,
           Fcons (id "C_flag",uint8,
           Fcons (id "V_flag",uint8,
           Fcons (id "Q_flag",uint8,
           Fcons (id "J_flag",uint8,
           Fcons (id "GE0",uint8,
           Fcons (id "GE1",uint8,
           Fcons (id "GE2",uint8,
           Fcons (id "GE3",uint8,
           Fcons (id "E_flag",uint8,
           Fcons (id "A_flag",uint8,
           Fcons (id "I_flag",uint8,
           Fcons (id "F_flag",uint8,
           Fcons (id "T_flag",uint8,
           Fcons (id "mode",int32,
           Fcons (id "background",uint32,
           Fnil))))))))))))))))), noattr)

(* Type representation of struct SLv6_SystemCoproc *)
let tp_sc =
  Tstruct (id "SLv6_SystemCoproc",
           Fcons (id "ee_bit",uint8,
           Fcons (id "u_bit",uint8,
           Fcons (id "v_bit",uint8,
           Fnil))), noattr)

(* Type representation of struct SLv6_Processor *)
let tp_proc =
  Tstruct (id "SLv6_Processor", 
           Fcons (id "mmu_ptr",Tpointer (tp_mmu,noattr),
           Fcons (id "cpsr",tp_sr,
           Fcons (id "spsrs",Tarray (tp_sr,num "5", noattr),
           Fcons (id "cp15",tp_sc,
           Fcons (id "id",uint32,
           Fcons (id "user_regs",Tarray (uint32,num "16", noattr),
           Fcons (id "fiq_regs",Tarray (uint32,num "7", noattr),
           Fcons (id "irq_regs",Tarray (uint32,num "2", noattr),
           Fcons (id "svc_regs",Tarray (uint32,num "2", noattr),
           Fcons (id "abt_regs",Tarray (uint32,num "2", noattr),
           Fcons (id "und_regs",Tarray (uint32,num "2", noattr),
           Fcons (id "pc",Tpointer (uint32, noattr),
           Fcons (id "jump",uint8,
           Fnil))))))))))))), noattr);;

(* Type representation of function reg *)
let tp_reg = 
  Tfunction(Tcons(Tpointer (tp_proc, noattr),Tcons(uint8,Tnil)),uint32);;

(* Type representation of function reg_m *)
let tp_regm = 
  Tfunction(Tcons(Tpointer (tp_proc, noattr),Tcons(uint8,Tcons(int32,Tnil))),uint32)
;;

(* Type representation of function get_bits*)
let tp_gbits = 
  Tfunction(Tcons(uint32,Tcons(uint32,Tcons(uint32,Tnil))),uint32);;

(* Type representation of function get_bit*)
let tp_gbit = 
  Tfunction(Tcons(uint32,Tcons(uint32,Tnil)),int8);;

(* Type representation of reg setting functions*)
let tp_setreg =
  Tfunction(Tcons(Tpointer (tp_proc, noattr),Tcons(uint8,Tcons(uint32,Tnil))),Tvoid);;
let tp_setpc = 
  Tfunction(Tcons(Tpointer (tp_proc, noattr),Tcons(uint32,Tnil)),Tvoid)
let tp_setregm =
  Tfunction(Tcons(Tpointer (tp_proc, noattr),Tcons(uint8,Tcons(int32,Tcons(uint32,Tnil)))),Tvoid)
let tp_setf =
  Tfunction(Tcons(Tpointer(uint32, noattr),Tcons(uint32,Tcons(uint32,Tcons(uint32,Tnil)))),Tvoid)
let tp_setb =
  Tfunction(Tcons(Tpointer(uint32, noattr),Tcons(uint32,Tcons(uint8,Tnil))),Tvoid)

(* Type representation of get spsr*)
let tp_spsr = Tfunction(Tcons(Tpointer (tp_proc, noattr),Tnil),Tpointer (tp_sr, noattr))
let tp_spsrm = Tfunction(Tcons(Tpointer (tp_proc, noattr),Tcons(int32,Tnil)),Tpointer (tp_sr, noattr))

(* Type representation of StatusRegister setting functions *)
let tp_setsr = Tfunction(Tcons(Tpointer (tp_sr, noattr),Tcons(uint32,Tnil)),Tvoid)
let tp_copysr = Tfunction(Tcons(Tpointer (tp_sr, noattr),Tcons(Tpointer (tp_sr, noattr),Tnil)),Tvoid)
let tp_srtoui32 = Tfunction(Tcons(Tpointer (tp_sr, noattr),Tnil),uint32)

let tp_read t =
  Tfunction(Tcons(Tpointer (tp_mmu, noattr),Tcons(uint32,Tnil)),
           (match t with
              |Byte->uint8
              |Half->Tint(I16,Unsigned, noattr)
              |Word->uint32));;

let lval_rval e = 
  match e with
    |(Evar _|Ederef _|Efield _) as a->Evalof (a, typeof a)
    |(Ecall _|Ebinop _|Eval _
      |Eparen _|Eloc _|Ecomma _|Epostincr _
      |Eassignop _|Eassign _|Esizeof _|Ealignof _|Econdition _|Ecast _
      |Eunop _|Eaddrof _|Evalof _) as a-> a
;;

let implicit_arg = function
  |"ConditionPassed" ->
     Econs(Eaddrof(Efield(Ederef(lval_rval(Evar(id "proc",Tpointer (tp_proc, noattr))),
                                 tp_proc),id "cpsr",tp_sr),Tpointer (tp_sr, noattr)),Enil)
  |"write_word" | "write_half" | "write_byte" ->
     Econs(Efield(lval_rval(Evar(id "proc",Tpointer (tp_proc, noattr))),id "mmu_ptr",tp_mmu),
           Enil)
  |"CP15_reg1_EEbit"|"CP15_reg1_Ubit"|"CP15_reg1_Vbit" -> 
     Econs(Eaddrof(Efield(lval_rval(Evar(id "proc",Tpointer (tp_proc, noattr))),
                          id "cp15",tp_sc),tp_sc),Enil)
  |"InAPrivilegedMode"|"CurrentModeHasSPSR"|"address_of_next_instruction"
  |"address_of_current_instruction"|"high_vectors_configured"|"set_reg_m" ->
     Econs(lval_rval(Evar(id "proc",Tpointer (tp_proc, noattr))),Enil)
  |_ -> Enil

let implicit_type = function
  |"ConditionPassed" -> 
     Tfunction(Tcons(Tpointer (tp_sr, noattr),Tcons(int32,Tnil)),int8)
  |"InAPrivilegedMode"|"CurrentModeHasSPSR"|"high_vectors_configured" -> 
     Tfunction(Tcons(Tpointer (tp_proc, noattr),Tnil),int8)
  |"address_of_next_instruction"|"address_of_current_instruction"->
     Tfunction(Tcons(Tpointer (tp_proc, noattr),Tnil),uint32)
  |"CarryFrom_add3"->
     Tfunction(Tcons(uint32,Tcons(uint32,Tcons(uint32,Tnil))),int8)
  |"OverflowFrom_add3"->
     Tfunction(Tcons(uint32,Tcons(uint32,Tcons(int8,Tnil))),int8)
  |"SignedDoesSat32_add"|"SignedDoesSat32_sub"|"SignedDoesSat32_double"->
     Tfunction(Tcons(int32,Tcons(int32,Tnil)),int8)
  |"SignExtend_30"|"SignExtend16"|"SignExtend8"|"ZeroExtend"->
     Tfunction(Tcons(uint32,Tnil),uint32)
  |"SignedSat"|"SignedDoesSat"|"UnsignedSat"|"UnsignedDoesSat"->
     Tfunction(Tcons(int32,Tcons(uint32,Tnil)),uint32)
  |_ -> Tvoid
;;

let implicit_ret = function
  |"ConditionPassed"|"CurrentModeHasSPSR"|"InAPrivilegedMode"
  |"CarryFrom_add3"|"OverflowFrom_add3"
  |"SignedDoesSat32_add"|"SignedDoesSat32_sub"|"SignedDoesSat32_double"-> 
     int8
  |"address_of_next_instruction"|"address_of_current_instruction"
  |"SignExtend_30"|"SignExtend16"|"SignExtend8"|"ZeroExtend"
  |"SignedSat32_add"|"SignedSat32_sub"|"SignedSat32_double"
  |"SignedSat"|"SignedDoesSat"|"UnsignedSat"|"UnsignedDoesSat"->
     uint32
  |_ -> Tvoid
;;

let rec acc_exprlist elst1 elst2 =
  match elst1 with
    | Enil -> elst2
    | Econs(r1,rl1) -> Econs(r1,acc_exprlist rl1 elst2)

(* Transformation form Pseudocode expr to CompcertC expr*)
let rec exp_trans = function
  |Num str -> Eval (Values.Vint (num str),int32)
  |Hex str -> Eval (Values.Vint (hex str),int32)
  |Bin str -> Eval (Values.Vint (bin str),int32)
  |Float_zero -> Eval (Values.Vfloat (B754_zero false),Tfloat (F32, noattr))
  |Var str -> lval_rval (Evar (id str,type_of_var str))
  |If_exp (e1, e2, e3) -> 
     Econdition (lval_rval(exp_trans e1),lval_rval(exp_trans e2),
                 lval_rval(exp_trans e3),int32)
  |BinOp (e1, str, e2) -> 
     (match str with
        |"and"->
           coq_Eseqand (lval_rval(exp_trans e1)) (lval_rval(exp_trans e2))
             (typeof (exp_trans e2))
        |"or"->
           coq_Eseqor (lval_rval(exp_trans e1)) (lval_rval(exp_trans e2))
             (typeof (exp_trans e2))
        |"<<"->
           Ebinop (binop_trans str,(lval_rval(exp_trans e1)),
                    (lval_rval(exp_trans e2)),(typeof (exp_trans e1)))
        |_->Ebinop (binop_trans str,(lval_rval(exp_trans e1)),
                    (lval_rval(exp_trans e2)),(typeof (exp_trans e2))))
  |Unpredictable_exp -> 
     Ecall (lval_rval(Evar(id "unpredictable",
                      Tfunction(Tnil,Tvoid))),Enil,
            Tvoid)
  |Memory (e,n) -> 
     Ecall(lval_rval(Evar(id ("read_"^(access_type n)),tp_read n)),
           Econs(exp_trans e,Enil), 
           (match n with
              |Byte->uint8
              |Half->Tint(I16,Unsigned, noattr)
              |Word->uint32))
  |Reg (Var s,None) -> 
     if List.mem s input_registers then
       lval_rval (Evar (id ("old_R"^s),uint32))
     else Ecall(lval_rval(Evar(id "reg",tp_reg)),
            Econs(lval_rval(Evar(id "proc",Tpointer (tp_proc, noattr))), 
            Econs(lval_rval(Evar(id s,uint8)),
            Enil)),uint32)
  |Reg (e,None)->
     Ecall (lval_rval(Evar(id "reg",tp_reg)),
            Econs(lval_rval(Evar(id "proc",Tpointer (tp_proc, noattr))), 
            Econs(lval_rval(exp_trans e),Enil)),uint32)
  |Reg (e,Some m) ->
     Ecall (lval_rval(Evar(id "reg_m",tp_regm)),
            Econs (lval_rval (Evar (id "proc",Tpointer (tp_proc, noattr))), 
            Econs (lval_rval (exp_trans e),
            Econs (lval_rval (Evar (id (mode m),int32)),
            Enil))),uint32)
  |Coproc_exp (e,f,es) ->
     Ecall (lval_rval(Evar (id f, uint32)),
            Econs (lval_rval(exp_trans e),
                   explst es),typeof(exp_trans e))
  (*|Fun(("CarryFrom_add3"|"OverflowFrom_add3") as f,_)->
     Ecall (lval_rval(Evar (id f,implicit_type f)),
            
                  (Econs(lval_rval(Evar(id ("old_Rn"),uint32)),
                   Econs(lval_rval(Evar(id "shifter_operand",uint32)),
                   Econs(lval_rval(Efield(Efield(Ederef
                               (lval_rval(Evar(id "proc",Tpointer (tp_proc, noattr))),tp_proc),
                                              id "cpsr",tp_sr),id ("C_flag"),uint8)),
                   Enil))))
            ,(implicit_ret f))*)
  |Fun(f,es)->
     Ecall(lval_rval(Evar (id f,implicit_type f)),
           (acc_exprlist (implicit_arg f) (explst es)),(implicit_ret f))
  |CPSR->
     Ecall(lval_rval(Evar(id "StatusRegister_to_uint32",tp_srtoui32)),
           Econs(Eaddrof(Efield(Ederef(lval_rval(Evar(id "proc",Tpointer (tp_proc, noattr))),
                                       tp_proc),id "cpsr",tp_sr),tp_sr),Enil),uint32)
  |SPSR None ->
     Ecall(lval_rval(Evar(id "StatusRegister_to_uint32",tp_srtoui32)),
           Econs(Ecall(lval_rval(Evar(id "spsr",tp_spsr)),
                       Econs(lval_rval(Evar(id "proc",Tpointer (tp_proc, noattr))),Enil),
                       Tpointer (tp_sr, noattr)),
           Enil),uint32)
  |SPSR (Some m)->
     Ecall(lval_rval(Evar(id "StatusRegister_to_uint32",tp_srtoui32)),
           Econs(Ecall(lval_rval(Evar(id "spsr_m",tp_spsrm)),
                       Econs(lval_rval(Evar(id "proc",Tpointer (tp_proc, noattr))),
                       Econs(lval_rval(Evar(id (mode m),int32)),
                       Enil)),Tpointer (tp_sr, noattr)),
           Enil),uint32)
  |Range (e,Bits (n1,n2))->
     Ecall(lval_rval (Evar (id "get_bits",tp_gbits)),
           Econs (lval_rval (exp_trans e),
           Econs (Eval (Values.Vint (num n1),uint32),
           Econs (Eval (Values.Vint (num n2),uint32),Enil))),uint32)
  |Range (_,Flag (s,_))-> (*"proc->cpsr.%s_flag"*)
     Efield(Efield(Ederef(lval_rval(Evar(id "proc",Tpointer (tp_proc, noattr))),tp_proc),
                          id "cpsr",tp_sr),id (s^"_flag"),int8)
  |Range (CPSR,Index (Num n)) -> (*"proc->cpsr.%s"*)
     Efield(Efield(Ederef(lval_rval(Evar(id "proc",Tpointer (tp_proc, noattr))),tp_proc),
                          id "cpsr",tp_sr),id (cpsr_flag n),int8)
  |Range (e1,Index e2) ->
     Ecall(lval_rval(Evar(id "get_bit",tp_gbit)),
           Econs(lval_rval(exp_trans e1),Econs(lval_rval(exp_trans e2),Enil)),
           int8)
  |Unaffected -> Ecall(Evar(id "ETodo", Tvoid),Enil,Tvoid)

  |Old_CPSR->
       lval_rval (Evar (id ("old_CPSR"),uint32))

and explst = function
  |[] -> Enil
  |h::t -> Econs (lval_rval(exp_trans h),explst t)
;;

(* transformation from pseudocode instruction to CompcertC statement*)
let rec stm_trans = function
  |Block insts ->
      (match insts with
        |[] -> Sskip
        |[i] -> stm_trans i
        |i::is -> Ssequence (stm_trans i, stm_trans (Block is)))
  |Let (_, _, insts, _) -> stm_trans (Block insts)
  |Unpredictable -> Sdo(exp_trans Unpredictable_exp)
  |Assign (dst, src) -> assign dst src
  |Return e -> Sreturn (Some (exp_trans e))
  |Case (e,s,o) ->
     Sswitch (exp_trans e, switch_aux s o)
  |Coproc (e, f, es) -> 
     Sdo (Ecall (lval_rval(Evar (id f, Tvoid)),explst([e]@es), Tvoid))
  |For (counter,min,max,i) ->
     Sfor(Sdo(Eassign(lval_rval(Evar(id counter,uint32)),
                      (Eval(Values.Vint(num min),uint32)),uint32)),
          Ebinop(Olt,lval_rval(Evar(id counter,uint32)),
                 Eval(Values.Vint (num max),uint32),uint32),
          Sdo(Epostincr(Incr,lval_rval(Evar(id counter,uint32)),uint32)),
          stm_trans i)
  |Assert e ->Sdo(Ecall(lval_rval(Evar(id "_assert_fail", Tvoid)),
                        explst [e],Tvoid))
  |While (e,i) -> Sdowhile (lval_rval(exp_trans e),stm_trans i)
  |Proc (f,es) -> Sdo(Ecall(lval_rval(Evar(id f,(implicit_type f))),
                            (acc_exprlist (implicit_arg f) (explst es)),Tvoid))
  |If (e,i1,i2) -> 
     Sifthenelse(exp_trans e,stm_trans i1, 
                  (match i2 with
                   |None -> Sskip
                   |Some i -> stm_trans i))

(*specific cases for registers and ranges assignement*)
and assign dst src =
  match dst with
    |Reg(Var s,None) -> 
        (match s with
           |"d"-> Sdo(Ecall(lval_rval(Evar(id "set_reg_or_pc",tp_setreg)),
                            Econs(lval_rval(Evar(id "proc",Tpointer (tp_proc, noattr))),
                            Econs(lval_rval(Evar(id "d",uint8)),
                            Econs(lval_rval(exp_trans src),Enil))),Tvoid))
           |"15"-> Sdo(Ecall(lval_rval(Evar(id "set_pc_raw",tp_setpc)),
                             Econs(lval_rval(Evar(id "proc",Tpointer (tp_proc, noattr))),
                             Econs(lval_rval(exp_trans src),Enil)),Tvoid))
           |s -> Sdo(Ecall(lval_rval (Evar(id "set_reg",tp_setreg)),
                           Econs(lval_rval(Evar(id "proc",Tpointer (tp_proc, noattr))),
                           Econs(lval_rval(Evar(id s,int32)),
                           Econs(lval_rval(exp_trans src),Enil))),Tvoid)))
    |Reg(Num "15",None)->Sdo(Ecall(lval_rval(Evar(id "set_pc_raw",tp_setpc)),
                                   Econs(lval_rval(Evar(id "proc",Tpointer (tp_proc, noattr))),
                                   Econs(lval_rval(exp_trans src),Enil)),Tvoid))
    |Reg(Num n,None)->Sdo(Ecall(lval_rval(Evar(id "set_reg",tp_setreg)),
                                Econs(lval_rval(Evar(id "proc",Tpointer (tp_proc, noattr))),
                                Econs(lval_rval(Eval(Values.Vint(num n),int32)),
                                Econs(lval_rval(exp_trans src),Enil))),Tvoid))
    |Reg(Var s,Some m) -> 
       Sdo(Ecall(lval_rval(Evar(id "set_reg_m",tp_setregm)),
                 Econs(lval_rval(Evar(id "proc",Tpointer (tp_proc, noattr))),
                 Econs(lval_rval(Evar(id s,uint8)),
                 Econs(lval_rval(Evar(id (mode m),int32)),
                 Econs(lval_rval(exp_trans src),Enil)))),Tvoid))
    |Range (e1,Index e2) ->
        Sdo(Ecall(lval_rval(Evar(id "set_bit",tp_setb)), 
            Econs(lval_rval(exp_trans e1),Econs(lval_rval(exp_trans e2),
            Econs(lval_rval(exp_trans src),Enil))),Tvoid))
    |Range (e,Bits (n1, n2)) ->
        Sdo(Ecall(lval_rval(Evar(id "set_field",tp_setf)), 
            Econs(lval_rval(exp_trans e),
            Econs(Eval(Values.Vint(num n1),uint32),
            Econs(Eval(Values.Vint(num n2),uint32),Enil))),Tvoid))
    |Range (CPSR,Flag _)->(*"proc->cpsr.%s_flag = %a"*)
       Sdo(Eassign(exp_trans dst,exp_trans src,int8))
    |CPSR|Old_CPSR -> 
        (match src with
          |SPSR None -> (*"copy_StatusRegister(&proc->cpsr, spsr(proc))"*)
             Sdo(Ecall(lval_rval(Evar(id "copy_StatusRegister",tp_copysr)),
                       Econs(Eaddrof(Efield(Ederef
                             (lval_rval(Evar(id "proc",Tpointer (tp_proc, noattr))),
                              tp_proc),id "cpsr",tp_sr),Tpointer (tp_sr, noattr)),
                       Econs(Ecall(lval_rval(Evar(id "spsr",tp_spsr)),
                                   Econs(lval_rval(Evar(id "proc",Tpointer (tp_proc, noattr))),
                                   Enil),Tpointer (tp_sr, noattr)),
                       Enil)),Tvoid))
          |SPSR (Some m) -> (*"copy_StatusRegister(&proc->cpsr, spsr_m(proc,m))"*)
             Sdo(Ecall(lval_rval(Evar(id "copy_StatusRegister",tp_copysr)),
                       Econs(Eaddrof(Efield(Ederef
                             (lval_rval(Evar(id "proc",Tpointer (tp_proc, noattr))),
                              tp_proc),id "cpsr",tp_sr),Tpointer (tp_sr, noattr)),
                       Econs(Ecall(lval_rval(Evar(id "spsr_m",tp_spsrm)),
                             Econs(lval_rval(Evar(id "proc",Tpointer (tp_proc, noattr))),
                             Econs(lval_rval(Evar(id(mode m),int32)),Enil)),
                                   Tpointer (tp_sr, noattr)),
                       Enil)),Tvoid))
          |(Num _|Bin _|Hex _|Float_zero|If_exp _|Fun _|BinOp _|CPSR|Old_CPSR|Reg _
            |Var _|Range (_,Bits _)|Range (_,Flag _)|Range (_,Index _)
            |Unaffected|Unpredictable_exp|Memory _|Coproc_exp _) as e -> 
             Sdo(Ecall(lval_rval(Evar(id "set_StatusRegister",tp_setsr)),
                       Econs(lval_rval(exp_trans e),Enil),Tvoid)))
    |SPSR None ->
        (match src with
          |CPSR |Old_CPSR-> (*"copy_StatusRegister(spsr(proc), &proc->cpsr)"*)
             Sdo(Ecall(lval_rval(Evar(id "copy_StatusRegister",tp_copysr)),
                       Econs(Ecall(lval_rval(Evar(id "spsr",tp_spsr)),
                                   Econs(lval_rval(Evar(id "proc",Tpointer (tp_proc, noattr))),
                                   Enil),Tvoid),
                       Econs(Eaddrof(Efield(Ederef
                             (lval_rval(Evar(id "proc",Tpointer (tp_proc, noattr))),
                              tp_proc),id "cpsr",tp_sr),Tpointer (tp_sr, noattr)),
                       Enil)),Tvoid))
          |(Num _|Bin _|Hex _|Float_zero|If_exp _|Fun _|BinOp _|SPSR _|Reg _
            |Var _|Range (_,Bits _)|Range (_,Flag _)|Range (_,Index _)
            |Unaffected|Unpredictable_exp|Memory _|Coproc_exp _) as e -> 
             Sdo(Ecall(lval_rval(Evar(id "set_StatusRegister",tp_setsr)),
                       Econs(lval_rval(exp_trans e),Enil),Tvoid)))
    |SPSR (Some m) ->
        (match src with
          |CPSR |Old_CPSR -> (*"copy_StatusRegister(spsr_m(proc,m), &proc->cpsr)"*)
             Sdo(Ecall(lval_rval(Evar(id "copy_StatusRegister",tp_copysr)),
                       Econs(Ecall(lval_rval(Evar(id "spsr_m",tp_spsrm)),
                                   Econs(lval_rval(Evar(id "proc",Tpointer (tp_proc, noattr))),
                                   Econs(lval_rval(Evar(id (mode m),int32)),
                                   Enil)),Tvoid),
                       Econs(Eaddrof(Efield(Ederef
                             (lval_rval(Evar(id "proc",Tpointer (tp_proc, noattr))),
                              tp_proc),id "cpsr",tp_sr),Tpointer (tp_sr, noattr)),
                       Enil)),Tvoid))
          |(Num _|Bin _|Hex _|Float_zero|If_exp _|Fun _|BinOp _|SPSR _|Reg _
            |Var _|Range (_,Bits _)|Range (_,Flag _)|Range (_,Index _)
            |Unaffected|Unpredictable_exp|Memory _|Coproc_exp _) as e -> 
             Sdo(Ecall(lval_rval(Evar(id "set_StatusRegister",tp_setsr)),
                       Econs(lval_rval(exp_trans e),Enil),Tvoid)))
    |Memory (e,n) -> 
       Sdo(Ecall(lval_rval(Evar(id ("write_"^(access_type n)),tp_read n)),
                 Econs(lval_rval(exp_trans e),Enil), 
           (match n with
              |Byte->uint8
              |Half->Tint(I16,Unsigned,noattr)
              |Word->uint32)))
    |Num _|Bin _|Hex _|Float_zero|If_exp _|Fun _|BinOp _|Reg _|Var _|Range (_,Flag _)
    |Unaffected|Unpredictable_exp|Coproc_exp _ -> 
       Sdo(Eassign(lval_rval(exp_trans dst),lval_rval(exp_trans src),Tvoid))

and switch_aux s o =
  match s with
    |[] -> (match o with
              |None -> LSdefault
                 (Sdo (Ecall(lval_rval(Evar (id "abort",Tvoid)),Enil,Tvoid)))
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
        (*Coq_pair*)(id a, b) 
        :: aux t
  in aux l;;

(*declaration for loading old_R *)
let rec oldr_decl rs st =
  let aux r =
    Sdo(Eassign(Evar(id ("old_R"^r),uint32),
                Ecall(lval_rval(Evar (id "reg",tp_reg)),
                      Econs(lval_rval(Evar(id "proc",Tpointer (tp_proc, noattr))),
                      Econs(lval_rval(Evar(id r,uint8)),Enil)),
                      uint32),uint32))
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
    (List.map (fun x->(*Coq_pair*)(id("old_R"^x),uint32)) old_r)@ls_id in
  {fn_return = Tvoid;
   fn_params = ((*Coq_pair*) (id "proc",Tpointer ((tp_proc, noattr))))::gs_id;
   fn_vars = fvar;
   fn_body = oldr_decl old_r (stm_trans (p.pinst))};;

let fndef_trans p = Internal (fn_trans p);;

let fn_index p = (*Coq_pair*) (id p.pident.iname, fndef_trans p);;

let gvars = 
  {AST.gvar_info = Tarray (uint8,num "0",noattr) ;
   AST.gvar_init = [];
   AST.gvar_readonly = false;
   AST.gvar_volatile =false};;

(*pseudocode programe to clight program*)
let prog_trans ({ body = ps ; _ } : Ast.program) =
  { AST.prog_funct = List.map fn_index ps;
    AST.prog_main = id "main";
    AST.prog_vars = [(*Coq_pair*) (id "gvars",gvars)] };;
