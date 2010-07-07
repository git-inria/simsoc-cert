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
open Dec;;

let num = string;;

let hex_of_bin = function
  | "0b00" | "0b0" -> "0"
  | "0b01" | "0b1" -> "1"
  | "0b10" -> "2"
  | "0b11" -> "3"
  | "0b10111" -> "ARM_Processor::abt"
  | "0b10011" -> "ARM_Processor::svc"
  | _ -> "TODO_hex_of_bin";;

(** C++ types of usual variables *)

let type_of_var = function

  | "S" | "L" | "mmod" | "F" | "I" | "A" | "R" | "x" | "y" | "X" | "U" | "W"
  | "shifter_carry_out" | "shift" | "opcode25" | "E" -> "bool"

  | "signed_immed_24" | "H" | "shifter_operand" | "alu_out" | "target"
  | "data" | "value" | "diffofproducts" | "address" | "start_address"
  | "physical_address" | "operand" | "opcode" | "byte_mask" | "mask"
  | "sum" | "diff" | "operand1" | "operand2" | "product1" | "product2"
  | "temp" | "diff1" | "diff2" | "diff3" | "diff4" | "invalidhandler"
  | "jpc" | "index" | "end_address" | "new_Rn" -> "uint32_t"

  | "n" | "d" | "m" | "s" | "dHi" | "dLo" | "imod" | "immed_8" | "rotate_imm"
  | "field_mask" | "shift_imm" | "sat_imm" | "rotate" | "cp_num"
  | "immedH" | "immedL" | "offset_8" -> "uint8_t"

  | "cond" -> "ARM_Processor::Condition"
  | "mode" -> "ARM_Processor::Mode"
  | "register_list" | "offset_12" -> "uint16_t"
  | "accvalue" | "result" -> "uint64_t"
  | "processor_id" -> "size_t"
  | _ -> "TODO_type_of_var";;

(** List the variables of a prog *)

module G = struct

  type typ = string;;

  let global_type = type_of_var;;

  let type_of_size = function
    | Byte -> "uint8_t"
    | Half -> "uint16_t"
    | Word -> "uint32_t";;

  let local_type s e =
    match e with
      | Memory (_, n) -> type_of_size n
      | _ -> type_of_var s;;

  let case_type = "uint8_t";;

end;;

module V = Ast.Make(G);;

(** Generate the code corresponding to an expression *)

let func = function
  | "CP15_reg1_EEbit" -> "proc.cp15.get_reg1_EEbit"
  | "CP15_reg1_Ubit" -> "proc.cp15.get_reg1_Ubit"
  | "PrivMask" -> "proc.msr_PrivMask"
  | "UserMask" -> "proc.msr_UserMask"
  | "StateMask" -> "proc.msr_StateMask"
  | "UnallocMask" -> "proc.msr_UnallocMask"
  | "GE" -> "proc.cpsr.GE"
  | "v5_and_above" -> "proc.v5_and_above"
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
  | "Logical_Shift_Right" -> ">>"
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
  | _ -> "TODO_binop";;

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

let cpsr_field = function
  | "4", "0" -> "mode"
  | s1, s2 -> "TODO_cpsr_field_"^s1^"_"^s2;;

let access_type = function
  | Byte -> "byte"
  | Half -> "half"
  | Word -> "word";;

let optemps = ["index"; "offset_8"; "end_address"];;

let input_registers = ["n"; "m"; "s"];;

let rec exp b = function
  | Bin s -> string b (hex_of_bin s)
  | Hex s | Num s -> string b s
  | If_exp (e1, e2, e3) -> bprintf b "(%a? %a: %a)" exp e1 exp e2 exp e3
  | BinOp (e1, ("Rotate_Right"|"Arithmetic_Shift_Right" as op), e2) ->
      exp b (Fun (binop op, [e1; e2]))
  | BinOp (e, "<<", Num "32") ->
      bprintf b "(static_cast<uint64_t>(%a) << 32)" exp e
  | BinOp (e, ("<"|">=" as op), Num "0") ->
      bprintf b "(static_cast<int32_t>(%a) %s 0)" exp e op
  | BinOp (e1, op, e2) -> bprintf b "(%a %s %a)" exp e1 (binop op) exp e2
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
  | Var s -> string b s
  | Memory (e, n) -> bprintf b "proc.mmu.read_%s(%a)" (access_type n) exp e
  | Range (CPSR, Flag (s,_)) -> bprintf b "proc.cpsr.%s_flag" s
  | Range (CPSR, Index (Num s)) -> bprintf b "proc.cpsr.%s" (cpsr_flag s)
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
  | Coproc_exp (e, f, es) ->
      bprintf b "proc.coproc(%a)->%s(%a)" exp e (func f) (list ", " exp) es
  | _ -> string b "TODO(\"exp\")";;

(** Generate the body of an instruction function *)

let rec inst k b = function
  | Block _ | For _ | While _ | If _ | Case _ as i ->
      bprintf b "%a%a" indent k (inst_aux k) i
  | i -> bprintf b "%a%a;" indent k (inst_aux k) i

and inst_aux k b = function
  | Unpredictable -> string b "unpredictable()"
  | Affect (dst, src) -> affect k b dst src
  | Proc (f, es) -> bprintf b "%s(%a)" f (list ", " exp) es
  | Assert e -> bprintf b "assert(%a)" exp e
  | Coproc (e, f, es) ->
      bprintf b "proc.coproc(%a)->%s(%a)" exp e (func f) (list ", " exp) es

  | Block [] -> ()
  | Block (Block _ | For _ | While _ | If _ | Case _ as i :: is) ->
      bprintf b "%a\n%a" (inst_aux k) i (list "\n" (inst k)) is
  | Block (i :: is) ->
      bprintf b "%a;\n%a" (inst_aux k) i (list "\n" (inst k)) is

  | While (e, i) -> bprintf b "while (%a)\n%a" exp e (inst (k+2)) i

  | For (counter, min, max, i) ->
      bprintf b "for (size_t %s = %a; %s<%a; ++%s) {\n%a\n}"
        counter num min counter num max counter (inst (k+2)) i

  | Case (e, s) ->
      bprintf b "switch (%a) {\n%a%a}"
        exp e (list "" (case_aux k)) s indent k

  | If (e, (Block _|If _ as i), None) ->
      bprintf b "if (%a) {\n%a\n%a}" exp e (inst (k+2)) i indent k
  | If (e, i, None) -> bprintf b "if (%a)\n%a" exp e (inst (k+2)) i

  | If (e, (Block _|If _ as i1), Some (Block _|If _ as i2)) ->
      bprintf b "if (%a) {\n%a\n%a} else {\n%a\n%a}"
	exp e (inst (k+2)) i1 indent k (inst (k+2)) i2 indent k
  | If (e, (Block _|If _ as i1), Some i2) ->
      bprintf b "if (%a) {\n%a\n%a} else\n%a"
	exp e (inst (k+2)) i1 indent k (inst (k+2)) i2
  | If (e, i1, Some (Block _|If _ as i2)) ->
      bprintf b "if (%a)\n%a\n%aelse {\n%a\n%a}"
	exp e (inst (k+2)) i1 indent k (inst (k+2)) i2 indent k
  | If (e, i1, Some i2) ->
      bprintf b "if (%a)\n%a\n%aelse\n%a"
	exp e (inst (k+2)) i1 indent k (inst (k+2)) i2

and case_aux k b (n, i) =
  bprintf b "%acase %s:\n%a\n%abreak;\n"
    indent k (hex_of_bin n) (inst (k+2)) i indent (k+2)

and affect k b dst src =
  if src = Unpredictable_exp then string b "unpredictable()"
  else match dst with
    | Reg (Var "d", _) -> bprintf b
"if (d==ARM_Processor::PC)\n%aproc.set_pc_raw(%a);\n%aelse\n%aproc.reg(d) = %a"
        indent (k+2) exp src indent k indent (k+2) exp src
    | Reg (Num "15", None) -> bprintf b "proc.set_pc_raw(%a)" exp src
    | Reg (e, None) -> bprintf b "proc.reg(%a) = %a" exp e exp src
    | Reg (e, Some m) ->
	bprintf b "proc.reg(%a,%s) = %a" exp e (mode m) exp src
    | CPSR -> bprintf b "proc.cpsr = %a" exp src
    | SPSR _ as e -> bprintf b "%a = %a" exp e exp src
    | Var v -> bprintf b "%a = %a" exp (Var v) exp src
    | Range (CPSR, Flag (s,_)) ->
        bprintf b "proc.cpsr.%s_flag = %a" s exp src
    | Range (CPSR, Index (Num n)) ->
        bprintf b "proc.cpsr.%s = %a" (cpsr_flag n) exp src
    | Range (CPSR, Bits ("19", "18")) ->
        bprintf b "proc.cpsr.set_GE_32(%a)" exp src
    | Range (CPSR, Bits ("17", "16")) ->
        bprintf b "proc.cpsr.set_GE_10(%a)" exp src
    | Range (CPSR, Bits (n1, n2)) ->
        bprintf b "proc.cpsr.%s = %a" (cpsr_field (n1,n2)) exp src
    | Range (e1, Bits (n1, n2)) ->
        inst_aux k b (Proc ("set_field", [e1; Num n1; Num n2; src]))
    | Memory (addr, n) ->
        inst_aux k b (Proc ("proc.mmu.write_" ^ access_type n, [addr; src]))
    | Range (e, Index n) -> inst_aux k b (Proc ("set_bit", [e; n; src]))
    | _ -> string b "TODO(\"affect\")";;

(** Generate a function modeling an instruction of the processor *)

let variant b k = bprintf b "_%s" k;;

let prog_var b s = bprintf b "<%s>" s;;

let prog_arg b (v,t) = bprintf b "const %s %s" t v;;

let prog_out b (v,t) = bprintf b "%s &%s" t v;;

let local_decl b (v,t) = bprintf b "  %s %s;\n" t v;;

let inreg_load b s =
  bprintf b "  const uint32_t old_R%s = proc.reg(%s); (void)old_R%s;\n" s s s;;

let ident b i = bprintf b "%s%a" i.iname (option "" variant) i.ivariant;;

let comment b p = bprintf b "// %a\n" Genpc.name p;;

let arg_sep l l' = match l, l' with _::_, _::_ -> ",\n    " | _ -> "";;

let prog gs ls b p =
  let ss = List.fold_left (fun l (s, _) -> s::l) [] gs in
  let inregs = List.filter (fun x -> List.mem x input_registers) ss in
    match p.pkind with
      | Inst ->
          bprintf b "%avoid ARM_ISS::%a(%a)\n{\n%a%a%a\n}\n" comment p
            (list "_" ident) (p.pident :: p.pidents)
            (list ",\n    " prog_arg) gs
            (list "" inreg_load) inregs
            (list "" local_decl) ls
            (inst 2) p.pinst
      | Mode m ->
          let os = List.filter (fun (x, _) -> not (List.mem x optemps)) ls
          and ls' = List.filter (fun (x, _) -> List.mem x optemps) ls in
            bprintf b "%avoid ARM_ISS::M%d_%a(%a%s%a)\n{\n%a%a%a\n}\n" comment p
              m
              string p.pident.iname
              (list ",\n    " prog_arg) gs
              (arg_sep gs os)
              (list ",\n    " prog_out) os
              (list "" inreg_load) inregs
              (list "" local_decl) ls'
              (inst 2) p.pinst;;

let decl gs ls b p =
  match p.pkind with
    | Inst  ->
	bprintf b "  %a  void %a(%a);\n" comment p
          (list "_" ident) (p.pident :: p.pidents) (list ",\n    " prog_arg) gs
    | Mode m ->
	let os = List.filter (fun (x, _) -> not (List.mem x optemps)) ls in
          bprintf b "  %a  void M%d_%a(%a%s%a);\n" comment p
            m
            string p.pident.iname
            (list ",\n    " prog_arg) gs
            (arg_sep gs os)
            (list ",\n    " prog_out) os;;

let lsm_hack p =
  let rec inst = function
    | Block is -> Block (List.map inst is)
    | If (_, Affect (Reg (Var "n", None), e), None) -> Affect (Var "new_Rn", e)
    | i -> i
  in
    match p.pkind with
      | Inst when p.pident.iname = "LDM" || p.pident.iname = "STM" ->
	  (* add 'if (W) then Rn = new_Rn' at the end of the main 'if' *)
          let a = If(Var "W",Affect(Reg(Var"n",None),Var"new_Rn"),None) in
          let i = match p.pinst with
            | If (c, Block ids, None) -> If (c, Block (ids @ [a]), None)
            | Block ([x; If (c, Block ids, None)]) ->
		Block ([x; If (c, Block (ids @ [a]), None)])
            | _ -> raise (Failure ("Unexpected AST shape: " ^ p.pident.iname))
          in { p with pinst = i }
      | Mode 4 ->
	  (* replace 'If (...) then Rn = ...' by 'new_Rn = ...' *)
          { p with pinst = inst p.pinst }
      | _ -> p;;

let dec_split decs =
  let is = ref [] and es = ref [] and ms = Array.create 5 [] in
  let rec split l =
    match l with
      | e :: t -> (
          match add_mode (name e) with
            | DecMode i -> ms.(i-1) <- e::ms.(i-1)
            | DecInst -> is := e::!is
            | DecEncoding ->es := e::!es);
          split t
      | [] -> (!is, !es, ms)
  in split decs;;

let lib b (pcs, decs) =
  ignore decs;
  let b2 = Buffer.create 10000 in
  let decl_and_prog b p =
    let p = lsm_hack p in
    let gs, ls = V.vars p in
      bprintf b "%a\n" (decl gs ls) p;
      bprintf b2 "%a\n" (prog gs ls) p
  in
    bprintf b
"#include \"arm_iss_base.hpp\"\n\nstruct ARM_ISS: ARM_ISS_Base {\n\n%a};\n\n%a"
    (list "" decl_and_prog) pcs Buffer.add_buffer b2;;
