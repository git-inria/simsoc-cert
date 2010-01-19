(**
SimSoC-Cert, a library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

C++ code generator for simulation (see directory ../cxx)
*)

open Ast;;
open Printf;;
open Util;;

let num = string;;

let hex_of_bin = function
  | "0b00" | "0b0" -> "0"
  | "0b01" | "0b1" -> "1"
  | "0b10" -> "2"
  | "0b11" -> "3"
  | "0b10111" -> "ARM_Processor::abt"
  | "0b10011" -> "ARM_Processor::svc"
  | _ -> "TODO";;

(** C++ types of usual variables *)

let type_of_var = function

  | "S" | "L" | "mmod" | "F" | "I" | "A" | "R" | "x" | "y" | "X" | "shift"
  | "shifter_carry_out" -> "bool"

  | "signed_immed_24" | "H" | "shifter_operand" | "alu_out" | "target"
  | "data" | "value" | "diffofproducts" | "address" | "start_address"
  | "physical_address" | "operand" | "opcode" | "byte_mask" | "mask"
  | "sum" | "diff" | "operand1" | "operand2" | "product1" | "product2"
  | "temp" | "diff1" | "diff2" | "diff3" | "diff4" | "invalidhandler"
  | "jpc" -> "uint32_t"

  | "n" | "d" | "m" | "s" | "dHi" | "dLo" | "imod" | "immed_8" | "rotate_imm"
  | "field_mask" | "shift_imm" | "sat_imm" | "rotate" | "cp_num" -> "uint8_t"

  | "cond" -> "ARM_Processor::Condition"
  | "mode" -> "ARM_Processor::Mode"
  | "register_list" -> "uint16_t"
  | "accvalue" | "result" -> "uint64_t"
  | "processor_id" -> "size_t"
  | _ -> "TODO";;

(** List the variables of a prog *)

module G = struct

  type typ = string;;

  let local_type s e =
    match e with
      | Memory (_, "1") -> "uint8_t"
      | Memory (_, "2") -> "uint16_t"
      | Memory (_, "4") -> "uint32_t"
      | _ -> type_of_var s;;

end;;

module V = Preproc.Make(G);;

let prog_variables p =
  let gs, ls = V.vars p in
    StrSet.elements gs, StrMap.fold (fun s t l -> (s,t)::l) ls [];;

(** Generate the code corresponding to an expression *)

let func = function
  | "address_of_BKPT_instruction" -> "this_instr"
  | "address_of_the_instruction_after_the_branch_instruction"
  | "address_of_the_instruction_after_the_BLX_instruction"
  | "address_of_instruction_after_the_BLX_instruction"
  | "address_of_next_instruction_after_the_SWI_instruction" -> "next_instr"
  | s -> s;;

let mode m = "ARM_Processor::" ^ Genpc.string_of_mode m;;

let binop = function
  | "and" -> "&&"
  | "or" -> "||"
  | "AND" -> "&"
  | "OR" -> "|"
  | "EOR" -> "^"
  | "NOT" -> "~"
  | "Logical_Shift_Left" -> "<<"
  | "==" -> "=="
  | "!=" -> "!="
  | ">=" -> ">="
  | "<" -> "<"
  | "+" -> "+"
  | "-" -> "-"
  | "<<" -> "<<"
  | "*" -> "*"
  | "Rotate_Right" -> "rotate_right"
  | "Arithmetic_Shift_Right" -> "asr"
  | _ -> "TODO";;

let reg_id = function
  | "15" -> "ARM_Processor::PC"
  | "14" -> "ARM_Processor::LR"
  | "13" -> "ARM_Processor::SP"
  | n -> n;;

let cpsr_flag = function
  | "31" -> "N_flag"
  | "30" -> "Z_flag"
  | "29" -> "C_flag"
  | "28" -> "V_flag"
  | "27" -> "Q_flag"
  | "24" -> "J_flag"
  | "9" -> "E_flag"
  | "8" -> "A_flag"
  | "7" -> "I_flag"
  | "6" -> "F_flag"
  | "5" -> "T_flag"
  | _ -> "TODO";;

let cpsr_field = function
  | "4", "0" -> "mode"
  | _ -> "TODO";;

let access_type = function
  | "1" -> "byte"
  | "2" -> "half"
  | "4" -> "word"
  | _ -> "TODO";;

let var = function
  | "CP15_reg1_EEbit" -> "proc.cp15.get_reg1_EEbit()"
  | "CP15_reg1_Ubit" -> "proc.cp15.get_reg1_Ubit()"
  | "PrivMask" -> "proc.msr_PrivMask()"
  | "UserMask" -> "proc.msr_UserMask()"
  | "StateMask" -> "proc.msr_StateMask()"
  | "UnallocMask" -> "proc.msr_UnallocMask()"
  | "GE" -> "proc.cpsr.GE"
  | "v5_and_above" -> "proc.v5_and_above"
  | s -> s;;

let input_registers = ["n"; "m"; "s"];;

let rec exp b = function
  | Bin s -> string b (hex_of_bin s)
  | Hex s | Num s -> string b s
  | If (e1, e2, e3) -> bprintf b "(%a? %a: %a)" exp e1 exp e2 exp e3
  | BinOp (e1, ("Rotate_Right"|"Arithmetic_Shift_Right" as op), e2) ->
      exp b (Fun (binop op, [e1; e2]))
  | BinOp (e, "<<", Num "32") ->
      bprintf b "(static_cast<uint64_t>(%a) << 32)" exp e
  | BinOp (e1, op, e2) -> bprintf b "(%a %s %a)" exp e1 (binop op) exp e2
(*REMOVE  | BinOp (Reg (Var "d", None), ("=="|"!=" as op), Num ("14"|"15" as num)) ->
      bprintf b "d%s%s" op num*)
(*REMOVE:  | Fun ("is_even", [Reg (Var "d", None)]) -> string b "is_even(d)"*)
  | Fun (f, es) -> bprintf b "%s(%a)" (func f) (list ", " exp) es
  | CPSR -> string b "proc.cpsr"
  | SPSR None -> string b "proc.spsr()"
  | SPSR (Some m) -> bprintf b "proc.spsr(%s)" (mode m)
  | Reg (Var s, None) ->
      if List.mem s input_registers
      then bprintf b "old_R%s" s
      else bprintf b "proc.reg(%s)" s
  | Reg (e, None) -> bprintf b "proc.reg(%a)" exp e
  | Reg (e, Some m) -> bprintf b "proc.reg(%a,%s)" exp e (mode m)
  | Var str -> string b (var str)
  | Memory (e, num) -> bprintf b "proc.mmu.read_%s(%a)" (access_type num) exp e
  | Range (CPSR, Flag (s,_)) -> bprintf b "proc.cpsr.%s_flag" s
  | Range (e1, Index e2) -> bprintf b "((%a>>%a)&1)" exp e1 exp e2
  | Range (e, Bits (n1, n2)) ->
      begin match n1, n2 with
        | "15", "0" -> bprintf b "get_half_0(%a)" exp e
        | "31", "16" -> bprintf b "get_half_1(%a)" exp e
        | "7", "0" -> bprintf b "get_byte_0(%a)" exp e
        | "15", "8" -> bprintf b "get_byte_1(%a)" exp e
        | "23", "16" -> bprintf b "get_byte_2(%a)" exp e
        | "31", "24" -> bprintf b "get_byte_3(%a)" exp e
        | _ -> bprintf b "get_bits(%a,%s,%s)" exp e n1 n2
      end
  | Coproc_exp (e, fct, es) ->
      bprintf b "proc.coproc(%a)->%s(%a)" exp e (func fct) (list ", " exp) es
  | _ -> string b "TODO(\"exp\")";;

(** Generate the body of an instruction function *)

let rec inst b = function
  | Block is -> bprintf b "%a" (list "" inst) is
  | Unpredictable -> string b "unpredictable();\n"
  | Affect (dst, src) -> affect b dst src
  | IfThenElse (condition, i, None) ->
      bprintf b "if (%a) {\n%a}\n" exp condition inst i
  | IfThenElse (e, i1, Some i2) ->
      bprintf b "if (%a) {\n%a} else {\n%a}\n" exp e inst i1 inst i2
  | Proc ("MemoryAccess", _) -> string b "// MemoryAcess(B-bit, E-bit);\n"
  | Proc (f, es) -> bprintf b "%s(%a);\n" f (list ", " exp) es
  | While (e, i) -> bprintf b "while (%a)\n%a" exp e inst i
  | Assert e -> bprintf b "assert(%a);\n" exp e
  | For (counter, min, max, i) ->
      bprintf b "for (size_t %s = %a; %s<%a; ++%s) {\n%a}\n"
        counter num min counter num max counter inst i
  | Coproc (e, f, es) ->
      bprintf b "proc.coproc(%a)->%s(%a);\n" exp e (func f) (list ", " exp) es
  | _ -> string b "TODO(\"inst\");\n"

and affect b dst src =
  if src = UnpredictableValue then string b "unpredictable();\n"
  else match dst with
    | Reg (Var "d", _) -> bprintf b
"if (d==ARM_Processor::PC)\n proc.set_pc_raw(%a);\nelse\n proc.reg(d) = %a;\n"
        exp src exp src
    | Reg (Num "15", None) -> bprintf b "proc.set_pc_raw(%a);\n" exp src
    | Reg (e, None) -> bprintf b "proc.reg(%a) = %a;\n" exp e exp src
    | Reg (e, Some m) ->
	bprintf b "proc.reg(%a,%s) = %a;\n" exp e (mode m) exp src
    | Var v -> bprintf b "%a = %a;\n" exp (Var v) exp src
    | CPSR -> bprintf b "proc.cpsr = %a;\n" exp src
    | SPSR _ as e -> bprintf b "%a = %a;\n" exp e exp src
    | Range (CPSR, Flag (s,_)) ->
        bprintf b "proc.cpsr.%s_flag = %a;\n" s exp src
    | Range (CPSR, Index (Num num)) ->
        bprintf b "proc.cpsr.%s = %a;\n" (cpsr_flag num) exp src
    | Range (CPSR, Bits (num1, num2)) ->
        bprintf b "proc.cpsr.%s = %a;\n" (cpsr_field (num1,num2)) exp src
    | Range (e1, Bits (num1, num2)) ->
        inst b (Proc ("set_field", [e1; Num num1; Num num2; src]))
    | Memory (addr, num) ->
        inst b (Proc ("proc.mmu.write_" ^ access_type num, [addr; src]))
    | Range (e1, Index num1) ->
        inst b (Proc ("set_bit", [e1; num1; src]))
    | _ -> string b "TODO(\"affect\");\n";;

(** Generate a function modeling an instruction of the processor *)

let version_in_comment b k = bprintf b " (%s)" k;;

let version_in_name b k = bprintf b "_%s" k;;

let prog_var b s = bprintf b "<%s>" s;;

let prog_arg b s = bprintf b "const %s %s" (type_of_var s) s;;

let local_decl b (var, vtype) = bprintf b "%s %s;\n" vtype var;;

let inreg_load b s = bprintf b "const uint32_t old_R%s = proc.reg(%s);\n" s s;;

let ident_in_comment b i =
  bprintf b "%s%a%a" i.iname (list "" prog_var) i.ivars
    (option "" version_in_comment) i.iversion

let ident b i =
  bprintf b "%s%a" i.iname (option "" version_in_name) i.iversion;;

let comment b p =
  bprintf b "// %s %a\n"
    p.pref (list ", " ident_in_comment) (p.pident :: p.paltidents);;

(*FIXME: optimize: pass prog_variables as argument!*)

let prog b p =
  let parameters, locals = prog_variables p in
  let inregs = List.filter (fun x -> List.mem x input_registers) parameters in
    bprintf b "%avoid ARM_ISS::%a(%a) {\n%a%a%a}\n" comment p
      (list "_" ident) (p.pident :: p.paltidents)
      (list ",\n    " prog_arg) parameters
      (list "" inreg_load) inregs
      (list "" local_decl) locals
      inst p.pinst;;

let decl b p =
  let parameters, _ = prog_variables p in
    bprintf b "  %a  void %a(%a);\n" comment p
      (list "_" ident) (p.pident :: p.paltidents)
      (list ",\n    " prog_arg) parameters;;

let lib b ps =
  bprintf b
"#include \"arm_iss_base.hpp\"\n\nstruct ARM_ISS: ARM_ISS_Base {\n\n%a};\n\n%a"
    (list "\n" decl) ps
    (list "\n" prog) ps;;
