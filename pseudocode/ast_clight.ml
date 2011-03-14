(**
SimSoC-Cert, a library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Pseudocode abstract syntax tree for clight.
*)

open Util;;
open Ast;;

type cl_signedness = Signed | Unsigned;;

type cl_intsize = Ast.size;;

type cl_floatsize = F32 | F64;;

type cl_id = string;;

let input_registers = ["n"; "m"; "s"; "dLo"];;

let mode m = Genpc.string_of_mode m;;

let access_type = function
  | Byte -> "byte"
  | Half -> "half"
  | Word -> "word";;

type cl_typ =
  | Int of cl_signedness * cl_intsize
  | Float of cl_floatsize
  | Void
  (*| Array of typ * int*)
  | Pointer of cl_typ
  | Function of cl_typ
  | Struct of cl_id * cl_fieldlist
  | Union of cl_id * cl_fieldlist
  | Comp_pointer of cl_id
  | Other

and cl_fieldlist =
  | Fnil
  | Fcons of cl_id * cl_typ * cl_fieldlist
;;

type cl_var_type =
  | Pint of cl_signedness * cl_intsize
  | Pfloat of cl_floatsize
  | Pvoid
  | Pother
;;

type cl_exp =
  | Eid of cl_id
  | Eint of string
  | Efloat of string
  (*| Esizeof of typ*)
  | Eunop of string * cl_exp
  | Ebinop of cl_exp * string * cl_exp
  | Epointderef of cl_exp
  | Efieldacc of cl_exp * cl_id
  | Eaddrof of cl_exp
  | Etypecast of cl_typ * cl_exp
  | Econd of cl_exp * cl_exp * cl_exp
  | Efun of cl_exp(*func*) * cl_exp list(*args*)
  | ETODO
;;

type cl_statement =
  | Sskip
  | Svardel of cl_typ * cl_exp
  | Sassign of cl_exp * cl_exp
  | Sfuncall of cl_id option * cl_exp(*func*) * cl_exp list(*args*)
  | Sincrease of cl_exp
  | Ssequence of cl_statement * cl_statement
  | Sifthenelse of cl_exp * cl_statement * cl_statement
  | Swhile of cl_exp * cl_statement
  (*| Sdowhile*)
  | Sfor of cl_statement * cl_exp * cl_statement * cl_statement
  (*| Sbreak | Scontinue*)
  | Sreturn of cl_exp option
  | Sswitch of cl_exp * labeled_statement 
  (*| Slabel | Sgoto*)
  (*| Proc of string * exp list | Coproc of exp * string * exp list
  | Memory of exp * int_size*)
  | STODO
and labeled_statement =
  | SDefault of cl_statement
  | SCase of int * cl_statement * labeled_statement
;;

let rec typ_trans = function
  | Tint -> Int (Signed, Word)
  | Tlong -> Int (Signed, Word)
  | Tfloat -> Float F32
  | Tdouble -> Float F64
  | Tvoid -> Void
  | Tchar -> Int (Signed, Byte)
  | Tbool -> Int (Signed, Byte)
  | Tunsigned -> Int (Unsigned, Word)
  | Tunsigned_long -> Int (Unsigned, Word)
  | Tunsigned_char -> Int (Unsigned, Byte)
  | Tunsigned_short -> Int (Unsigned, Half)
  | Tunsigned_int -> Int (Unsigned, Word)
;;

let rec exp_trans e =
    match e with
  | Num str | Hex str -> Eint  str
  | Bin str -> Eint str
  | Float_zero -> Efloat "0.0"
  | If_exp (e1, e2, e3) -> Econd (exp_trans e1,exp_trans e2,exp_trans e3)
  | (Fun _ | CPSR | SPSR _) as s -> func_trans s
  | BinOp (e1, str, e2) -> Ebinop (exp_trans e1, str, exp_trans e2)
  | Reg (Var s, None) -> if List.mem s input_registers
      then Eid ("old_R"^s)
      else Efun (Eid "reg", [Eid "proc"; Eid s])
  | Reg _ as s -> func_trans s
  | Var str -> Eid str
  | Range (CPSR, Flag (s,_)) -> 
      Efieldacc (Efieldacc ((Epointderef (Eid "proc")), "cpsr"), s^"_flag")
  | Range (CPSR, Index (Num s)) -> 
      Efieldacc (Efieldacc ((Eid "proc"), "cpsr"), s)
  | Range _ as s ->
      func_trans s
  | Unaffected as s -> func_trans s
  | Unpredictable_exp as s -> func_trans s
  | Memory _ as s -> func_trans s 
  | Coproc_exp _ as s -> func_trans s

and func_trans (e : exp) =
  match e with 
    | Fun (str, elst) -> Efun (Eid str, List.map (exp_trans) elst)
    | CPSR -> Efun (Eid "StatusRegister_to_uint32", 
                    [Efieldacc (Eaddrof (Eid "proc"), "cpsr")])
    | SPSR None -> Efun (Eid "StatusRegister_to_uint32", [Eid "spsr(proc)"])
    | SPSR (Some m) ->
        Efun (Eid "StatusRegister_to_uint32", 
              [Eid ("spsr(proc,"^(mode m)^")")])
    | Reg (Var s, None) -> Efun (Eid "reg", [Eid "proc"; Eid s])
    | Reg (e, None) -> Efun (Eid "reg", [Eid "proc"; exp_trans e])
    | Reg (e, Some m) -> Efun (Eid "reg_m", [Eid "proc"; exp_trans e; Eid (mode m)])
    | Range (e1, Index e2) -> 
        Efun (Eid "get_bit", [exp_trans e1; exp_trans e2])
    | Unaffected | Unpredictable_exp -> Efun (Eid "unpredictable", [])
    | Memory (e, sz) -> 
        Efun (Eid ("read"^(access_type sz)), [Efieldacc (Eid "proc", "mmu_ptr");exp_trans e])
    | Coproc_exp (e, f, es) -> Efun (Eid f, 
                                     [Eid "proc"; exp_trans e]@List.map exp_trans es)
    | _ -> ETODO
;;

let rec stm_trans = function
  | Block instlst -> begin match instlst with
      | [] -> Sskip
      | inst :: insts -> Ssequence (stm_trans inst, stm_trans (Block insts))
    end
  | Let (_, _, instlst, _) ->
      stm_trans (Block instlst)
  | Unpredictable -> Sfuncall (None, Eid "unpredictable", [])
  | Affect (e1, e2) -> Sassign (exp_trans e1, exp_trans e2)
  | If (e1, inst1, Some inst2) -> Sifthenelse (exp_trans e1, stm_trans inst1, stm_trans inst2)
  | If (e1, inst1, None) -> Sifthenelse (exp_trans e1, stm_trans inst1, Sskip)
  | Proc (str, elst) -> Sfuncall (None, Eid str, List.map exp_trans elst)
  | While (e, inst) -> Swhile (exp_trans e, stm_trans inst)
  | For (count, min, max, inst) -> 
      Sfor (Sassign (Eid count, Eid min), Ebinop (Eid count, "<=", Eid max),
           Sincrease (Eid count), stm_trans inst)
  | Coproc _ -> STODO
  | Case _ -> STODO
  | Assert _ -> STODO
  | Return e -> Sreturn (Some (exp_trans e))
;;

let spcfun_trans = function
  | Sassign (Efun (Eid "reg", es), e) ->
      Sfuncall (None, Eid "set_reg_or_pc", es@ [e])
  (*| Sassign (Efun (Eid "reg", [Eid "proc"; e1]), e2) ->
      begin match e1 with
        | Eid "d" -> Sfuncall (None, Eid "set_reg_or_pc", [Eid "proc"; e1; e2])
        | _ -> Sfuncall (None, Eid "set_reg", [Eid "proc"; e1; e2])
      end*)
  | Sassign (Efun (Eid "StatusRegister_to_uint32", [es1]),
             Efun (Eid "StatusRegister_to_uint32", [es2])) ->
      Sfuncall (None, Eid "copy_StatusRegister", [es1] @ [es2])
  | s -> s
      

type cl_func = {
  func_return : cl_typ;
  func_params : (cl_id * cl_typ) list;
  func_vars : (cl_id * cl_var_type) list;
  func_tempvars : (cl_id * cl_var_type) list;
  func_body : cl_statement };; 

(*type func_type = 
  | Internal of func 
  | External of ;;*)

type cl_prog = {
  cl_pref : string; 
  cl_pkind : kind;
  cl_pid : string;
  cl_pident : ident;
  cl_pidents : ident list;
  cl_params : (string * string) list;
  cl_vars : (string * string) list;
  cl_tmpvars : (string * string) list;
  cl_pfuncs : cl_statement };;

type cl_program = {
  hd : Ast.inst list;
  bd : cl_prog list }
