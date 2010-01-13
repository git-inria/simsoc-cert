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

let bin_to_hex = function
  | "0b00" | "0b0" -> "0"
  | "0b01" | "0b1" -> "1"
  | "0b10" -> "2"
  | "0b11" -> "3"
  | "0b10111" -> "ARM_Processor::abt"
  | "0b10011" -> "ARM_Processor::svc"
  | _ -> "TODO";;

(** C++ types of usual variables *)

let cxx_type_of = function
  | "S" | "L" | "mmod" | "F" | "I" | "A" | "R" | "x" | "y" | "X" | "shift" -> "bool"
  | "signed_immed_24" | "H" -> "uint32_t"
  | "shifter_operand" -> "uint32_t"
  | "shifter_carry_out" -> "bool"
  | "alu_out" | "target" | "data" | "value" | "diffofproducts" -> "uint32_t"
  | "address" | "start_address" | "physical_address" | "operand" -> "uint32_t"
  | "opcode" | "byte_mask" | "mask" | "sum" | "diff" -> "uint32_t"
  | "operand1" | "operand2" | "product1" | "product2" | "temp" -> "uint32_t"
  | "diff1" | "diff2" | "diff3" | "diff4" -> "uint32_t"
  | "Rn" | "Rd" | "Rm" | "Rs" | "RdHi" | "RdLo" -> "uint8_t"
  | "cond" -> "ARM_Processor::Condition"
  | "mode" -> "ARM_Processor::Mode"
  | "imod" | "immed_8" | "rotate_imm" | "field_mask" -> "uint8_t"
  | "shift_imm" | "sat_imm" | "rotate" -> "uint8_t"
  | "register_list" -> "uint16_t"
  | "accvalue" | "result" -> "uint64_t"
  | "invalidhandler" | "jpc" -> "uint32_t"
  | "processor_id" -> "size_t"
  | _ -> "TODO";;

let input_registers = ["Rn"; "Rm"; "Rs"];;
let output_registers = ["Rd"; "RdHi"; "RdLo"; "Rn"];;

let specials = ["CP15_reg1_EEbit"; "Memory"; "Ri"; "Ri_usr";
                "CP15_reg1_Ubit"; "GE"; "i";
                "UnallocMask"; "StateMask"; "UserMask"; "PrivMask"]

(** List the variables of a prog *)

let var_type v expr =
  match expr with
    | Range (Var "Memory", Index [_; Num "1"]) -> "uint8_t"
    | Range (Var "Memory", Index [_; Num "2"]) -> "uint16_t"
    | Range (Var "Memory", Index [_; Num "4"]) -> "uint32_t"
    | _ -> cxx_type_of v;;

let rec exp_variables (parameters,locals) expression =
  match expression with
  | If (condition, expr1, expr2) ->
      let variables = exp_variables (parameters,locals) condition in
      let variables' = exp_variables variables expr1 in
        exp_variables variables' expr2
  | BinOp (expr1, _, expr2) ->
      let variables = exp_variables (parameters,locals) expr1 in
        exp_variables variables expr2
  | Fun (_, expressions) ->
      List.fold_left exp_variables (parameters,locals) expressions
  | Var str ->
      if (List.mem str parameters) ||
        (List.mem_assoc str locals) ||
        (List.mem str specials)
      then (parameters,locals)
      else (str::parameters,locals)
  | Range (expr1, Index (expr2::_)) ->
      let variables = exp_variables (parameters,locals) expr1 in
        exp_variables variables expr2
  | Range (expr, _) -> exp_variables (parameters,locals) expr
  | _ -> (parameters,locals);;

let rec inst_variables (parameters,locals) instruction =
  match instruction with
    | Block insructions ->
        List.fold_left inst_variables (parameters,locals) insructions
    | IfThenElse (condition, instruction, None) ->
        let variables = exp_variables (parameters,locals) condition in
          inst_variables variables instruction
    | IfThenElse (condition, instruction1, Some instruction2) ->
        let variables = exp_variables (parameters,locals) condition in
        let variables' = inst_variables variables instruction1 in
          inst_variables variables' instruction2
    | Proc (_, expressions) ->
        List.fold_left exp_variables (parameters,locals) expressions
    | While (condition, instruction) ->
        let variables = exp_variables (parameters,locals) condition in
          inst_variables variables instruction
    | For (_, _, _, instruction) ->
        inst_variables (parameters,locals) instruction
    | Affect (Var str, expr2) | Affect (Range (Var str, _), expr2) ->
        let variables =
          if (List.mem_assoc str locals) ||
            (List.mem str specials) ||
            (List.mem str parameters)
          then parameters, locals
          else
            if (List.mem str output_registers)
            then str::parameters, locals
            else parameters, (str, (var_type str expr2))::locals
        in
          exp_variables variables expr2
    | Affect (_, expr2) -> exp_variables (parameters,locals) expr2
    | _ -> (parameters,locals)

let prog_variables p =
  inst_variables ([],[]) p.pinst;;

(** Generate the code corresponding to an expression *)

let gen_fct = function
  | "B_address_of_the_instruction_after_the_branch_instruction" -> "next_instr"
  | "BKPT_address_of_BKPT_instruction" -> "this_instr"
  | "BLX1_address_of_the_instruction_after_the_BLX_instruction" -> "next_instr"
  | "BLX2_address_of_instruction_after_the_BLX_instruction" -> "next_instr"
  | "SWI_address_of_next_instruction_after_the_SWI_instruction" -> "next_instr"
  | "LDM1_architecture_version_5_or_above" -> "version_5_or_above"
  | "LDR_ARMv5_or_above" -> "version_5_or_above"
  | "BKPT_high_vectors_configured" -> "high_vectors_configured"
  | "SWI_high_vectors_configured" -> "high_vectors_configured"
  | str -> str;;

let mode = function
  | Fiq -> "ARM_Processor::fiq"
  | Irq -> "ARM_Processor::irq"
  | Svc -> "ARM_Processor::svc"
  | Abt -> "ARM_Processor::abt"
  | Und -> "ARM_Processor::und";;

let cxx_op = function
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
  | _ -> "TODO";;

let reg_id = function
  | "15" -> "ARM_Processor::PC"
  | "14" -> "ARM_Processor::LR"
  | "13" -> "ARM_Processor::SP"
  | num -> num;;

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

let generate_var = function
  | "Rd" -> "proc.reg(Rd)"
  | "RdHi" -> "proc.reg(RdHi)"
  | "RdLo" -> "proc.reg(RdLo)"
  | "Ri" -> "proc.reg(i)"
  | "Ri_usr" -> "proc.reg(i,ARM_Processor::usr)"
  | "Rn" -> "Rn_content"
  | "Rm" -> "Rm_content"
  | "Rs" -> "Rs_content"
  | "CP15_reg1_EEbit" -> "proc.cp15.get_reg1_EEbit()"
  | "CP15_reg1_Ubit" -> "proc.cp15.get_reg1_Ubit()"
  | "PrivMask" -> "proc.msr_PrivMask()"
  | "UserMask" -> "proc.msr_UserMask()"
  | "StateMask" -> "proc.msr_StateMask()"
  | "UnallocMask" -> "proc.msr_UnallocMask()"
  | "GE" -> "proc.cpsr.GE"
  | str -> str;;

let rec generate_exp buffer expression =
  match expression with
  | Bin s -> string buffer (bin_to_hex s)
  | Hex s | Num s -> string buffer s
  | If (condition, expr1, expr2) -> bprintf buffer "(%a? %a: %a)"
      generate_exp condition generate_exp expr1 generate_exp expr2
  | BinOp (Var "Rd", "==", Num "15") -> string buffer "Rd==ARM_Processor::PC"
  | BinOp (Var "Rd", "is", Reg ("15", None)) -> string buffer "Rd==ARM_Processor::PC"
  | BinOp (Var "Rd", "is_not", Reg ("14", None)) -> string buffer "Rd!=ARM_Processor::LR"
  | BinOp (expr1, "Rotate_Right", expr2) ->
      generate_exp buffer (Fun ("rotate_right", [expr1; expr2]))
  | BinOp (expr1, "<<", Num "32") ->
      bprintf buffer "(static_cast<uint64_t>(%a) << 32)"
      generate_exp expr1
  | BinOp (expr1, "Arithmetic_Shift_Right", expr2) ->
      generate_exp buffer (Fun ("asr", [expr1; expr2]))
  | BinOp (expr1, op, expr2) ->
      bprintf buffer "(%a %s %a)"
      generate_exp expr1 (cxx_op op) generate_exp expr2
  | Fun ("is_even_numbered", [Var "Rd"]) -> string buffer "!(Rd&1)"
  | Fun (fct, expressions) ->
      bprintf buffer "%s(%a)"
        (gen_fct fct) (list ", " generate_exp) expressions
  | CPSR -> string buffer "proc.cpsr"
  | SPSR None -> string buffer "proc.spsr()"
  | SPSR (Some m) -> bprintf buffer "proc.spsr(%s)" (mode m)
  | Reg (n, None) -> bprintf buffer "proc.reg(%s)" (reg_id n)
  | Reg (n, Some m) -> bprintf buffer "proc.reg(%s,%s)"(reg_id n) (mode m)
  | Var str -> string buffer (generate_var str)
  | RdPlus1 -> string buffer "proc.reg(Rd+1)"
  | Range (CPSR, Flag (str1,_)) ->
      bprintf buffer "proc.cpsr.%s_flag" str1
  | Range (expr1, Index [expr2]) ->
      bprintf buffer "((%a>>%a)&1)"
      generate_exp expr1 generate_exp expr2
  | Range (Var "Memory", Index [expr; Num num]) ->
      bprintf buffer "proc.mmu.read_%s(%a)"
        (access_type num) generate_exp expr
  | Range (expr, Bits (num1, num2)) -> (
      match num1, num2 with
        | "15", "0" -> bprintf buffer "get_half_0(%a)" generate_exp expr
        | "31", "16" -> bprintf buffer "get_half_1(%a)" generate_exp expr
        | "7", "0" -> bprintf buffer "get_byte_0(%a)" generate_exp expr
        | "15", "8" -> bprintf buffer "get_byte_1(%a)" generate_exp expr
        | "23", "16" -> bprintf buffer "get_byte_2(%a)" generate_exp expr
        | "31", "24" -> bprintf buffer "get_byte_3(%a)" generate_exp expr
        | _ -> bprintf buffer "get_bits(%a,%s,%s)"
            generate_exp expr num1 num2
    )
  | _ -> string buffer "TODO(\"?\")";;

(** Generate the body of an instruction function *)

let rec generate_inst buffer instruction =
  match instruction with
    | Block insructions ->
        bprintf buffer "%a"
          (list "" generate_inst) insructions
    | Unpredictable -> string buffer "unpredictable();\n"
    | Affect (dst, src) -> generate_affect buffer dst src
    | IfThenElse (condition, instruction, None) ->
        bprintf buffer "if (%a) {\n%a}\n"
          generate_exp condition
          generate_inst instruction
    | IfThenElse (condition, instruction1, Some instruction2) ->
        bprintf buffer "if (%a) {\n%a} else {\n%a}\n"
          generate_exp condition
          generate_inst instruction1
          generate_inst instruction2
    | Proc ("MemoryAccess", _) -> string buffer "// MemoryAcess(B-bit, E-bit);\n"
    | Proc (fct, expressions) ->
        bprintf buffer "%s(%a);\n" fct
        (list ", " generate_exp) expressions
    | While (condition, instruction) ->
        bprintf buffer "while (%a)\n%a"
          generate_exp condition
          generate_inst instruction
    | Assert expr ->
        bprintf buffer "assert(%a);\n"
          generate_exp expr
    | For (counter, min, max, instruction) ->
        bprintf buffer "for (size_t %s = %a; %s<%a; ++%s) {\n%a}\n"
          counter num min counter num max counter
          generate_inst instruction
    | _ -> string buffer "TODO(\"?\");\n"

and generate_affect buffer dst src =
  match src with
    | Fun ("LDRH_UnpredictableValue", []) -> string buffer "unpredictable();\n"
    | Fun ("LDRSH_UnpredictableValue", []) -> string buffer "unpredictable();\n"
    | Fun ("STRH_UnpredictableValue", []) -> string buffer "unpredictable();\n"
    | _ -> (
        match dst with
          | Var "Rd" -> bprintf buffer
         "if (Rd==ARM_Processor::PC)\n proc.set_pc_raw(%a);\nelse\n proc.reg(Rd) = %a;\n"
                generate_exp src generate_exp src
          | Var "Rn" ->
              bprintf buffer "proc.reg(Rn) = %a;\n" generate_exp src
          | Var v ->
              bprintf buffer "%a = %a;\n" generate_exp (Var v) generate_exp src
          | CPSR ->
              bprintf buffer "proc.cpsr = %a;\n" generate_exp src
          | SPSR _ as expr1 ->
              bprintf buffer "%a = %a;\n" generate_exp expr1 generate_exp src
          | Range (CPSR, Flag (str1,_)) ->
              bprintf buffer "proc.cpsr.%s_flag = %a;\n" str1 generate_exp src
          | Range (CPSR, Index [Num num]) ->
              bprintf buffer "proc.cpsr.%s = %a;\n" (cpsr_flag num) generate_exp src
          | Range (CPSR, Bits (num1, num2)) ->
              bprintf buffer "proc.cpsr.%s = %a;\n"
                (cpsr_field (num1,num2)) generate_exp src
          | Range (expr1, Bits (num1, num2)) ->
              generate_inst buffer
                (Proc ("set_field", [expr1; Num num1; Num num2; src]))
          | Range (Var "Memory", Index [addr; Num num]) ->
              let fct = "proc.mmu.write_" ^ (access_type num) in
                generate_inst buffer (Proc (fct, [addr; src]))
          | Range (expr1, Index [num1]) ->
              generate_inst buffer
                (Proc ("set_bit", [expr1; num1; src]))
          | (Reg ("15", None)) ->
              bprintf buffer "proc.set_pc_raw(%a);\n" generate_exp src
          | (Reg ("15", Some _)) ->
              string buffer "TODO(\"set_pc_with_mode\");\n"
          | (Reg (num, None)) ->
              bprintf buffer "proc.reg(%s) = %a;\n" (reg_id num) generate_exp src
          | (Reg (num, Some m)) ->
              bprintf buffer "proc.reg(%s,%s) = %a;\n"
                (reg_id num) (mode m) generate_exp src
          | RdPlus1 ->
              bprintf buffer "proc.reg(Rd+1) = %a;\n" generate_exp src
          | _ -> string buffer "TODO(\"Affect\");\n"
      );;

(** Generate a function modeling an instruction of the processor *)

let version_in_comment b k = bprintf b " (%s)" k;;

let version_in_name b k = bprintf b "_%s" k;;

let prog_var b s = bprintf b "<%s>" s;;

let prog_arg buffer str =
  bprintf buffer "const %s %s" (cxx_type_of str) str;;

let generate_local_decl buffer (var, vtype) =
  bprintf buffer "%s %s;\n" vtype var;;

let generate_inreg_load buffer str =
  bprintf buffer "const uint32_t %s_content = proc.reg(%s);\n" str str;;

let ident_in_comment b i =
  bprintf b "%s%a%a" i.iname (list "" prog_var) i.ivars
    (option version_in_comment) i.iversion

let ident b i =
  bprintf b "%s%a" i.iname (option version_in_name) i.iversion

let generate_comment buffer p =
  bprintf buffer "// %s %a\n"
    p.pref (list ", " ident_in_comment) (p.pident::p.paltidents);;

let generate_prog buffer p =
  let parameters, locals = prog_variables p in
  let inregs = List.filter (fun x -> List.mem x input_registers) parameters in
    bprintf buffer
      "%avoid ARM_ISS::%a(%a) {\n%a%a%a}\n"
      generate_comment p
      (list "_" ident) (p.pident :: p.paltidents)
      (list ",\n    " prog_arg) parameters
      (list "" generate_inreg_load) inregs
      (list "" generate_local_decl) locals
      generate_inst p.pinst;;

let generate_decl buffer p =
  let parameters, _ = prog_variables p in
    bprintf buffer
      "  %a  void %a(%a);\n"
      generate_comment p
      (list "_" ident) (p.pident :: p.paltidents)
      (list ",\n    " prog_arg) parameters;;

let lib buffer progs =
  bprintf buffer
    "#include \"arm_iss_base.hpp\"\n\nstruct ARM_ISS: ARM_ISS_Base {\n\n%a};\n\n%a"
    (list "\n" generate_decl) progs
    (list "\n" generate_prog) progs;;
