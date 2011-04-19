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

(* Type representation of struct SLv6_MMU *)
let tp_mmu =
  Tstruct (id "SLv6_MMU",
           Fcons (id "begin",Tint (I32,Unsigned),
           Fcons (id "size",Tint (I32,Unsigned),
           Fcons (id "end",Tint (I32,Unsigned),
           Fcons (id "mem",Tpointer (Tint (I8,Unsigned)),
           Fnil)))))
(* Type representation of struct SLv6_StatusRegister *)
let tp_sr = 
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

(* Type representation of struct SLv6_SystemCoproc *)
let tp_sc =
  Tstruct (id "SLv6_SystemCoproc",
           Fcons (id "ee_bit",Tint (I8,Unsigned),
           Fcons (id "u_bit",Tint (I8,Unsigned),
           Fcons (id "v_bit",Tint (I8,Unsigned),
           Fnil))))

(* Type representation of struct SLv6_Processor *)
let tp_proc =
  Tstruct (id "SLv6_Processor", 
           Fcons (id "mmu_ptr",Tpointer (tp_mmu),
           Fcons (id "cpsr",tp_sr,
           Fcons (id "spsrs",Tarray (tp_sr,num "5"),
           Fcons (id "cp15",tp_sc,
           Fcons (id "id",Tint (I8,Unsigned),
           Fcons (id "user_regs",Tarray (Tint (I32,Unsigned),num "16"),
           Fcons (id "fiq_regs",Tarray (Tint (I32,Unsigned),num "7"),
           Fcons (id "irq_regs",Tarray (Tint (I32,Unsigned),num "2"),
           Fcons (id "svc_regs",Tarray (Tint (I32,Unsigned),num "2"),
           Fcons (id "abt_regs",Tarray (Tint (I32,Unsigned),num "2"),
           Fcons (id "und_regs",Tarray (Tint (I32,Unsigned),num "2"),
           Fcons (id "pc",Tpointer (Tint (I32,Unsigned)),
           Fnil)))))))))))));;

(* Type representation of function reg *)
let tp_reg = 
  Tfunction(Tcons(Tpointer tp_proc,Tcons(Tint(I8,Unsigned),Tnil)),Tint(I32,Unsigned));;

(* Type representation of function reg_m *)
let tp_regm = 
  Tfunction(Tcons(Tpointer tp_proc,Tcons(Tint(I8,Unsigned),Tcons(Tint(I8,Unsigned),Tnil))),Tint (I32,Unsigned))
;;

(* Type representation of function get_bits*)
let tp_gbits = 
  Tfunction(Tcons(Tint(I32,Unsigned),Tcons(Tint(I32,Unsigned),Tcons(Tint(I32,Unsigned),Tnil))),Tint (I32,Unsigned));;

(* Type representation of function get_bit*)
let tp_gbit = 
  Tfunction(Tcons(Tint(I32,Unsigned),Tcons(Tint(I32,Unsigned),Tnil)),Tint (I8,Unsigned));;

(* Type representation of reg setting functions*)
let tp_setreg =
  Tfunction(Tcons(Tpointer tp_proc,Tcons(Tint(I8,Unsigned),Tcons(Tint(I32,Unsigned),Tnil))),Tvoid);;
let tp_setpc = 
  Tfunction(Tcons(Tpointer tp_proc,Tcons(Tint(I32,Unsigned),Tnil)),Tvoid)
let tp_setregm =
  Tfunction(Tcons(Tpointer tp_proc,Tcons(Tint(I8,Unsigned),Tcons(Tint(I8,Unsigned),Tcons(Tint(I32,Unsigned),Tnil)))),Tvoid)
let tp_setf =
  Tfunction(Tcons(Tpointer(Tint(I32,Unsigned)),Tcons(Tint(I32,Unsigned),Tcons(Tint(I32,Unsigned),Tcons(Tint(I32,Unsigned),Tnil)))),Tvoid)
let tp_setb =
  Tfunction(Tcons(Tpointer(Tint(I32,Unsigned)),Tcons(Tint(I32,Unsigned),Tcons(Tint(I8,Unsigned),Tnil))),Tvoid)

(* Type representation of get spsr*)
let tp_spsr = Tfunction(Tcons(Tpointer tp_sr,Tnil),tp_sr)
let tp_spsrm = Tfunction(Tcons(Tpointer tp_sr,Tcons(Tint(I8,Unsigned),Tnil)),tp_sr)

(* Type representation of StatusRegister setting functions *)
let tp_setsr = Tfunction(Tcons(Tpointer tp_sr,Tcons(Tint(I32,Unsigned),Tnil)),Tvoid)
let tp_copysr = Tfunction(Tcons(Tpointer tp_sr,Tcons(Tpointer tp_sr,Tnil)),Tvoid)
let tp_srtoui32 = Tfunction(Tcons(Tpointer tp_sr,Tnil),Tint(I32,Unsigned))

let tp_read t =
  Tfunction(Tcons(Tpointer tp_mmu,Tcons(Tint(I32,Unsigned),Tnil)),
           (match t with
              |Byte->Tint(I8,Unsigned)
              |Half->Tint(I16,Unsigned)
              |Word->Tint(I32,Unsigned)));;

let implicit_arg = function
  |"ConditionPassed" ->
     Econs(Eaddrof(Efield(Ederef(Evalof(Evar(id "proc",tp_proc),tp_proc),tp_sr),id "cpsr",tp_sr),tp_sr),Enil)
  |"write_word" | "write_half" | "write_byte" ->
     Econs(Efield(Evalof(Evar(id "proc",tp_proc),tp_proc),id "mmu_ptr",tp_mmu),Enil)
  |"CP15_reg1_EEbit"|"CP15_reg1_Ubit"|"CP15_reg1_Vbit" -> 
     Econs(Eaddrof(Efield(Evalof(Evar(id "proc",tp_proc),tp_proc),id "cp15",tp_sc),tp_sc),Enil)
  |"InAPrivilegedMode"|"CurrentModeHasSPSR"|"address_of_next_instruction"
  |"address_of_current_instruction"|"high_vectors_configured"|"set_reg_m" ->
     Econs(Evalof(Evar(id "proc",tp_proc),tp_proc),Enil)
  |_ -> Enil

let implicit_type = function
  |"ConditionPassed" -> 
     Tfunction(Tcons(Tpointer tp_proc,Tcons(Tint(I32,Unsigned),Tnil)),Tint(I8,Unsigned))
  |"InAPrivilegedMode"|"CurrentModeHasSPSR"|"high_vectors_configured" -> 
     Tfunction(Tcons(Tpointer tp_proc,Tnil),Tint(I8,Unsigned))
  |"address_of_next_instruction"|"address_of_current_instruction"->
     Tfunction(Tcons(Tpointer tp_proc,Tnil),Tint(I32,Unsigned))
  |_ -> Tvoid
;;

let rec acc_exprlist elst1 elst2 =
  match elst1 with
    | Enil -> elst2
    | Econs(r1,rl1) -> Econs(r1,acc_exprlist rl1 elst2)

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
  |Memory (e,n) -> 
     Ecall(Evalof(Evar(id ("read_"^(access_type n)),tp_read n),tp_read n),
           Econs(exp_trans e,Enil), 
           (match n with
              |Byte->Tint(I8,Unsigned)
              |Half->Tint(I16,Unsigned)
              |Word->Tint(I32,Unsigned)))
  |Reg (Var s,None) -> 
     if List.mem s input_registers then
       Evalof (Evar (id ("old_R"^s),Tint (I32,Unsigned)),Tint(I32,Unsigned))
     else Ecall (Evalof (Evar (id "reg",tp_reg),tp_reg),
            Econs (Evalof (Evar (id "proc",tp_proc),tp_proc), 
            Econs (Evalof (Evar (id s,Tint (I8,Unsigned)),Tint (I8,Unsigned)),
            Enil)),Tint (I32,Unsigned))
  |Reg (e,None)->
     Ecall (Evalof (Evar (id "reg",tp_reg),tp_reg),
            Econs (Evalof (Evar (id "proc",tp_proc),tp_proc), 
            Econs (Evalof (exp_trans e,typeof (exp_trans e)), Enil)),Tint (I32,Unsigned))
  |Reg (e,Some m) ->
     Ecall (Evalof (Evar (id "reg_m",tp_regm),tp_regm),
            Econs (Evalof (Evar (id "proc",tp_proc),tp_proc), 
            Econs (Evalof (exp_trans e,typeof (exp_trans e)),
            Econs (Evalof (Evar (id (mode m),Tint (I32,Unsigned)),Tint (I32,Unsigned)),
            Enil))),Tint (I32,Unsigned))
  |Coproc_exp (e,f,es) ->
     Ecall (Evalof (Evar (id f, Tint (I32,Unsigned)),Tint (I32,Unsigned)),
            Econs (Evalof (exp_trans e,typeof (exp_trans e)),
                   explst es),typeof (exp_trans e))
  |Fun (f,es)->
     Ecall (Evalof (Evar (id f,implicit_type f),(implicit_type f)),
            (acc_exprlist (implicit_arg f) (explst es)),(implicit_type f))
  |CPSR->
     Ecall (Evalof (Evar (id "StatusRegister_to_uint32",tp_srtoui32),tp_srtoui32),
            Econs (Eaddrof (Efield (Ederef (Evalof (Evar (id "proc",tp_proc),tp_proc),tp_sr),id "cpsr",tp_sr),tp_sr),Enil),Tint (I32,Unsigned))
  |SPSR None ->
     Ecall (Evalof (Evar (id "StatusRegister_to_uint32",tp_srtoui32),tp_srtoui32),
            Econs (Ecall (Evalof (Evar (id "spsr",tp_sr),tp_sr),
                          Econs (Evalof (Evar (id "proc",tp_proc),tp_proc),Enil),Tint (I32,Unsigned)),Enil),Tint (I32,Unsigned))
  |SPSR (Some m)->
     Ecall (Evalof (Evar (id "StatusRegister_to_uint32",tp_srtoui32),tp_srtoui32),
            Econs (Ecall (Evalof (Evar (id "spsr_m",tp_sr),tp_sr),
                          Econs (Evalof (Evar (id "proc",tp_proc),tp_proc),
                          Econs (Evalof (Evar (id (mode m),tp_proc),tp_proc),Enil)),Tint (I32,Unsigned)),Enil),Tint (I32,Unsigned))
  |Range (e,Bits (n1,n2))->
     Ecall (Evalof (Evar (id "get_bits",tp_gbits),tp_gbits),
            Econs (Evalof (exp_trans e,typeof (exp_trans e)),
            Econs (Eval (Values.Vint (num n1),Tint (I32,Unsigned)),
            Econs (Eval (Values.Vint (num n2),Tint (I32,Unsigned)),Enil))),Tint (I32,Unsigned))
  |Range (_,Flag (s,_))-> (*"proc->cpsr.%s_flag"*)
     Efield (Efield (Evar (id "proc",tp_proc),id "cpsr",tp_sr),id (s^"_flag"), Tint (I8,Unsigned))
  |Range (CPSR,Index (Num n)) -> (*"proc->cpsr.%s"*)
     Efield (Efield (Evar (id "proc",tp_proc),id "cpsr",tp_sr),id (cpsr_flag n), Tint (I8,Unsigned))
  |Range (e1,Index e2) ->
     Ecall (Evalof (Evar (id "get_bit",tp_gbit),tp_gbit),
            Econs (exp_trans e1,Econs (exp_trans e2,Enil)),Tint (I32,Unsigned))
  |Unaffected -> Ecall (Evar (id "ETodo", Tvoid),Enil,Tvoid)

and explst = function
  |[] -> Enil
  |h::t -> Econs (Evalof (exp_trans h,typeof (exp_trans h)),explst t)
;;

(* transformation from pseudocode instruction to CompcertC statement*)
let rec stm_trans = function
  |Block insts ->
      (match insts with
        |[] -> Sskip
        |[i] -> stm_trans i
        |i::is -> Ssequence (stm_trans i, stm_trans (Block is)))
  |Let (_, _, insts, _) -> stm_trans (Block insts)
  |Unpredictable -> Sdo (Ecall (Evar (id "unpredictable", Tvoid),Enil,Tvoid))
  |Affect (dst, src) -> affect dst src
  |Return e -> Sreturn (Some (exp_trans e))
  |Case (e,s,o) ->
     Sswitch (exp_trans e, switch_aux s o)
  |Coproc (e, f, es) -> 
     Sdo (Ecall (Evalof (Evar (id f, Tvoid),Tvoid),explst ([e]@es), Tvoid))
  |For (counter,min,max,i) ->
     Sfor(Sdo(Eassign(Evalof(Evar(id counter,Tint(I32,Unsigned)),Tint(I32,Unsigned)),
                      (Eval(Values.Vint(num min),Tint(I32,Unsigned))),Tint(I32,Unsigned))),
          Ebinop(Olt,Evalof(Evar(id counter,Tint(I32,Unsigned)),Tint(I32,Unsigned)),
                 Eval(Values.Vint (num max),Tint(I32,Unsigned)),Tint(I32,Unsigned)),
          Sdo(Epostincr(Incr,Evalof(Evar(id counter,Tint(I32,Unsigned)),Tint(I32,Unsigned)),Tint(I32,Unsigned))),
           stm_trans i)
  |Assert e -> Sdo (Ecall (Evar (id "_assert_fail", Tvoid),explst [e],Tvoid))
  |While (e,i) -> Sdowhile (exp_trans e,stm_trans i)
  |Proc (f,es) -> Sdo(Ecall(Evalof(Evar(id f,(implicit_type f)),(implicit_type f)),
                            (acc_exprlist (implicit_arg f) (explst es)),Tvoid))
  |If (e,i1,i2) -> 
     Sifthenelse(exp_trans e,stm_trans i1, 
                  (match i2 with
                   |None -> Sskip
                   |Some i -> stm_trans i))

(*specific cases for registers and ranges assignement*)
and affect dst src =
  match dst with
    |Reg(Var s,None) -> 
        (match s with
           |"d"-> Sdo (Ecall (Evalof (Evar (id "set_reg_or_pc",tp_setreg),tp_setreg),
                              Econs (Evalof (Evar (id "proc",tp_proc),tp_proc),
                              Econs (Evalof (Evar (id "d",Tint (I8,Unsigned)),Tint (I8,Unsigned)),
                              Econs (exp_trans src,Enil))),Tvoid))
           |"15"-> Sdo (Ecall (Evalof(Evar (id "set_pc_raw",tp_setpc),tp_setpc),
                               Econs (Evalof (Evar (id "proc",tp_proc),tp_proc),Enil),Tvoid))
           |s -> Sdo (Ecall (Evalof (Evar (id "set_reg",tp_setreg),tp_setreg),
                             Econs (Evalof (Evar (id "proc",tp_proc),tp_proc),
                             Econs (Evalof (Evar (id s,Tint (I8,Unsigned)),Tint (I8,Unsigned)),
                             Econs (exp_trans src,Enil))),Tvoid)))
    |Reg (Var s,Some m) -> 
       Sdo (Ecall (Evalof (Evar (id "set_reg_m",tp_setregm),tp_setregm),
            Econs (Evalof (Evar (id "proc",tp_proc),tp_proc),
            Econs (Evalof (Evar (id s,Tint(I8,Unsigned)),Tint(I8,Unsigned)),
            Econs (Evalof (Evar (id (mode m),Tint(I8, Unsigned)),Tint(I8, Unsigned)),
            Econs (exp_trans src,Enil)))),Tvoid))
    |Range (e1,Index e2) ->
        Sdo(Ecall(Evalof(Evar(id "set_bit",tp_setb),tp_setb), 
            Econs(exp_trans e1,Econs(exp_trans e2,Econs(exp_trans src,Enil))),Tvoid))
    |Range (e,Bits (n1, n2)) ->
        Sdo(Ecall(Evalof(Evar(id "set_field",tp_setf),tp_setf), 
            Econs (exp_trans e,
            Econs (Eval (Values.Vint (num n1),Tint (I32,Unsigned)),
            Econs (Eval (Values.Vint (num n2),Tint (I32,Unsigned)),Enil))),Tvoid))
    |CPSR -> 
        (match src with
          |SPSR None -> (*"copy_StatusRegister(&proc->cpsr, spsr(proc))"*)
             Sdo(Ecall(Evalof(Evar(id "copy_StatusRegister",tp_setsr),tp_setsr),
                 Econs(Eaddrof(Efield(Ederef(Evalof(Evar(id "proc",tp_proc),tp_proc),tp_sr),id "cpsr",tp_sr),tp_sr),
                 Econs(Ecall(Evalof(Evar(id "spsr",tp_sr),tp_sr),Econs(Evalof(Evar(id "proc",tp_proc),tp_proc),Enil),tp_sr),
                 Enil)),Tvoid))
          |SPSR (Some m) -> (*"copy_StatusRegister(&proc->cpsr, spsr_m(proc,m))"*)
             Sdo(Ecall(Evalof(Evar(id "copy_StatusRegister",tp_spsrm),tp_spsrm),
                 Econs(Eaddrof(Efield(Ederef(Evalof(Evar(id "proc",tp_proc),tp_proc),tp_sr),id "cpsr",tp_sr),tp_sr),
                 Econs(Ecall(Evalof(Evar(id "spsr_m",tp_setsr),tp_setsr),
                             Econs(Evalof(Evar(id "proc",tp_proc),tp_proc),
                             Econs(Evalof(Evar(id(mode m),Tint(I8,Unsigned)),Tint(I8,Unsigned)),Enil)),tp_sr),
                 Enil)),Tvoid))
          |(Num _|Bin _|Hex _|Float_zero|If_exp _|Fun _|BinOp _|CPSR|Reg _|Var _|Range (_,Bits _)
          |Range (_,Flag _)|Range (_,Index _)|Unaffected|Unpredictable_exp|Memory _|Coproc_exp _) as e -> 
             Sdo(Ecall(Evalof(Evar(id "set_StatusRegister",tp_setsr),tp_setsr),Econs(exp_trans e,Enil),Tvoid)))
    |SPSR None ->
        (match src with
          |CPSR -> (*"copy_StatusRegister(spsr(proc), &proc->cpsr)"*)
             Sdo(Ecall(Evalof(Evar(id "copy_StatusRegister",tp_copysr),tp_copysr),
                       Econs(Ecall(Evalof(Evar(id "spsr",tp_spsr),tp_spsr),Econs(Evar(id "proc",tp_proc),Enil),Tvoid),
                       Econs(Eaddrof(Efield(Ederef(Evalof(Evar(id "proc",tp_proc),tp_proc),tp_sr),id "cpsr",tp_sr),tp_sr),
                       Econs(Ecall(Evalof(Evar(id "spsr",tp_spsr),tp_spsr),Econs(Evalof(Evar(id "proc",tp_proc),tp_proc),Enil),tp_sr),
                       Enil))),Tvoid))
          |(Num _|Bin _|Hex _|Float_zero|If_exp _|Fun _|BinOp _|SPSR _|Reg _|Var _|Range (_,Bits _)
          |Range (_,Flag _)|Range (_,Index _)|Unaffected|Unpredictable_exp|Memory _|Coproc_exp _) as e -> 
             Sdo(Ecall(Evalof(Evar(id "set_StatusRegister",tp_setsr),tp_setsr),Econs(exp_trans e,Enil),Tvoid)))
    |SPSR (Some m) ->
        (match src with
          |CPSR -> (*"copy_StatusRegister(spsr_m(proc,m), &proc->cpsr)"*)
             Sdo(Ecall(Evalof(Evar(id "copy_StatusRegister",tp_copysr),tp_copysr),
                       Econs(Ecall(Evalof(Evar(id "spsr_m",tp_spsrm),tp_spsrm),
                                   Econs(Evalof(Evar(id "proc",tp_proc),tp_proc),
                                   Econs(Evalof(Evar(id (mode m),Tint(I32,Unsigned)),Tint(I32,Unsigned)),Enil)),Tvoid),
                       Econs(Eaddrof(Efield(Ederef(Evalof(Evar(id "proc",tp_proc),tp_proc),tp_sr),id "cpsr",tp_sr),tp_sr),
                       Econs(Ecall(Evalof(Evar(id "spsr",tp_spsr),tp_spsr),Econs(Evalof(Evar(id "proc",tp_proc),tp_proc),Enil),tp_spsr),
                       Enil))),Tvoid))
          |(Num _|Bin _|Hex _|Float_zero|If_exp _|Fun _|BinOp _|SPSR _|Reg _|Var _|Range (_,Bits _)
          |Range (_,Flag _)|Range (_,Index _)|Unaffected|Unpredictable_exp|Memory _|Coproc_exp _) as e -> 
             Sdo(Ecall(Evalof(Evar(id "set_StatusRegister",tp_sr),tp_sr),Econs (exp_trans e,Enil),Tvoid)))
    |Memory (e,n) -> 
       Sdo(Ecall(Evalof(Evar(id ("write_"^(access_type n)),tp_read n),tp_read n),
           Econs(exp_trans e,Enil), 
           (match n with
              |Byte->Tint(I8,Unsigned)
              |Half->Tint(I16,Unsigned)
              |Word->Tint(I32,Unsigned))))
    |Num _|Bin _|Hex _|Float_zero|If_exp _|Fun _|BinOp _|Reg _|Var _|Range (_,Flag _)
    |Unaffected|Unpredictable_exp|Coproc_exp _  -> 
       Sdo(Eassign(exp_trans dst,exp_trans src,Tvoid))

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
    Sdo(Eassign(Evar(id ("old_R"^r),Tint(I32,Unsigned)),
                Ecall(Evalof(Evar (id "reg",tp_reg),tp_reg),
                      Econs(Evalof(Evar(id "proc",tp_proc),tp_proc),
                      Econs(Evalof(Evar(id r,Tint(I8,Unsigned)),Tint(I8,Unsigned)),Enil)),
                      Tint(I32,Unsigned)),Tint(I32,Unsigned)))
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
    (List.map (fun x->Coq_pair(id("old_R"^x),Tint (I32,Unsigned))) old_r)@ls_id in
  {fn_return = Tvoid;
   fn_params = (Coq_pair (id "proc",Tpointer (tp_proc)))::gs_id;
   fn_vars = fvar;
   fn_body = oldr_decl old_r (stm_trans (p.pinst))};;

let fndef_trans p = Internal (fn_trans p);;

let fn_index p = Coq_pair (id p.pident.iname, fndef_trans p);;

let gvars = 
  {AST.gvar_info = Tarray (Tint(I8,Unsigned),num "0") ;
   AST.gvar_init = [];
   AST.gvar_readonly = false;
   AST.gvar_volatile =false};;

(*pseudocode programe to clight program*)
let prog_trans ({ body = ps ; _ } : Ast.program) =
  { AST.prog_funct = List.map fn_index ps;
    AST.prog_main = id "main";
    AST.prog_vars = [Coq_pair (id "gvars",gvars)] };;
