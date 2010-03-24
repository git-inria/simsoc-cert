(**
SimSoC-Cert, a library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Coq code generator for simulation (see directory ../coq)
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
  | "0b10111" -> "abt"
  | "0b10011" -> "svc"
  | "0b10000" -> "usr"
  | "0b10001" -> "fiq"
  | "0b10010" -> "irq"
  | "0b11011" -> "und"
  | "0b11111" -> "sys"
  | _ -> "TODO0";;

(*coq types of usual var*)

let type_of_var = function
  | "cond" -> "opcode"
  | "mode" -> "processor_mode"
  | "S" | "L" | "F" | "I" | "A" | "R" | "shifter_carry_out" | "shift" | "mmod"
	-> "bool"
  | "shifter_operand" | "shift_imm" | "immed_8" | "signed_immed_24"
      -> "word"
  | "n" | "d" | "m" | "s" | "" -> "reg_num"

  | "st" -> "state"
  | "md" -> "processor_mode"

  | _ -> "TODO0";;

module G = struct

  type typ = string;;

  let global_type = type_of_var;;

  let local_type s e =
    match e with
      | Memory (_, "1") -> "byte"
      | Memory (_, "2") -> "halfword"
      | Memory (_, "4") -> "word"
      | _ -> type_of_var s;;

  let key_type = "word";;

end;;

module V = Preproc.Make(G);;

let variables p =
  let gs, ls = V.vars p in
    (StrMap.fold (fun s t l -> (s,t)::l) gs [],
     StrMap.fold (fun s t l -> (s,t)::l) ls []);;

let num_word = function
  | "0" -> "w0"
  | "1" -> "w1"
  | "2" -> "w2"
  | _ -> "TODO1";;

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
  | _ -> "TODO2";;

let reg_id = function
  | "15" -> "PC"
  | "14" -> "LR"
  | "13" -> "SP"
  | n -> n;;

let func = function
  | "address of the instruction after the BLX instruction"
  | "address_of_the_instruction_after_the_branch_instruction"
  | "address_of_instruction_after_the_BLX_instruction"
  | "address_of_next_instruction_after_the_SWI_instruction"
    -> "next_inst_address s"
  | "ConditionPassed" -> "ConditionPassed (cpsr s)"
  | "CurrentModeHasSPSR" -> "CurrentModeHasSPSR s"
  | "SignExtend_30" -> "SignExtend"
  | s -> s;;

let mode m = Genpc.string_of_mode m;;

let binop = function
  | "AND" -> "and"
  | "OR" -> "or"
  | "EOR" -> "xor"
  | "NOT" -> "not"
  | "and" -> "&&"
  | "or" -> "||"
  | "+" -> "add"
  | "-" -> "sub"
  | "*" -> "mul"
  | "==" -> "zeq"
  | "!=" -> "zne"
  | ">=" -> "zge"
  | "<" -> "not zge"
  | "Logical_Shift_Left" | "<<" -> "Logical_Shift_Left"
  | "Logical_Shift_Right"| ">>" -> "Logical_Shift_Right"
  | "Arithmetic_Shift_Right" -> "Arithmetic_Shift_Right"
  | "Rotate_Right" -> "Rotate_right" 
  | _ -> "TODO4";;

let cpsr_field = function
  | "4", "0" -> "mode"
  | "19", "16" -> "GE"
  | _ -> "TODO5";;

let access_type = function
  | "1" -> "byte"
  | "2" -> "half"
  | "4" -> "word"
  | _ -> "TODO6";;

let var = function
  | "CP15_reg1_EEbit" -> "proc.cp15.get_reg1_EEbit()"
  | "CP15_reg1_Ubit" -> "proc.cp15.get_reg1_Ubit()"
  | "PrivMask" -> "PrivMask"
  | "UserMask" -> "UserMask"
  | "StateMask" -> "StateMask"
  | "UnallocMask" -> "UnallocMask"
  | "GE" -> "(cpsr s)[19#16]"
  | "v5_and_above" -> "proc.v5_and_above"
  | s -> s;;

let input_registers = ["n"; "m"; "s"];;

let optemps = ["index"; "offset_8"; "end_address"];;

let rec exp b = function
  | Bin s -> string b (hex_of_bin s)
  | Hex s | Num s -> string b s
  | CPSR -> string b "cpsr"
  | SPSR None -> string b "spsr s"
  | SPSR (Some m) -> bprintf b "spsr s %s" (mode m)
  | Memory (e, n) -> bprintf b "Memory %s %a" (access_type n) exp e
  | BinOp (e1, ("Rotate_Right"|"Arithmetic_Shift_Right" | "Logical_Shift_left"
	   | "Logical_Shift_Right" | "+" | "-" | "*" | "AND" | "OR" | "EOR"
	   | "==" | "!=" | ">=" | "<" | ">>" as op), e2) ->
      exp b (Fun (binop op, [e1; e2]))
  | BinOp (e, "<<", Num "32") ->
      bprintf b "(static_cast<uint64_t>(%a) << 32)" exp e 
  | BinOp (e1, op, e2) -> bprintf b "(%a) %s (%a)" exp e1 (binop op) exp e2
  | Fun (f, es) -> bprintf b "%s %a" (func f) (list " " exp) es

  | If_exp (e1, e2, e3) -> bprintf b "if (%a) then %a else %a" exp e1 exp e2 exp e3
 
  | Reg (Var s, None) ->
      if List.mem s input_registers
      then bprintf b "(reg_content s %s)" s
      else bprintf b "(reg_content s %s)" s
  | Reg (Num n, None) -> bprintf b "(reg_content s %s)" (reg_id n)
  | Reg (e, None) -> bprintf b "(reg_content s R%a)" exp e
  | Reg (e, Some m) -> bprintf b "reg_of_mode %a %s" exp e (mode m)
  | Range (CPSR, Flag (s,_)) -> bprintf b "(cpsr s)[%sbit]" s
  | Range (e1, Index e2) -> bprintf b "%a[%a]" exp e1 exp e2
  
  | Range (e, Bits (n1, n2)) ->
      begin match n1, n2 with
        | "15", "0" -> bprintf b "%a[15#0]" exp e
        | "31", "16" -> bprintf b "%a[31#16]" exp e
        | "7", "0" -> bprintf b "%a[7#0]" exp e
        | "15", "8" -> bprintf b "%a[15#8]" exp e
        | "23", "16" -> bprintf b "%a[23#16]" exp e
        | "31", "24" -> bprintf b "%a[31#24]" exp e
        | _ -> bprintf b "%a[%s#%s]" exp e n1 n2
      end
  | Coproc_exp (e, f, es) ->
      bprintf b "proc.coproc(%a)->%s(%a)" exp e (func f) (list ", " exp) es
  | Var str -> string b (var str)
 
  | _ -> string b "TODO6";;

let rec inst k b = function
  | Block _ | For _ | While _ | If _ | Case _ as i ->
      bprintf b "%a%a" Genpc.indent (k) (inst_aux (k+2)) i
  | i -> bprintf b "%a%a" Genpc.indent (k) (inst_aux (k+2)) i

and inst_aux k b = function
  | Unpredictable -> string b "Unpredictable"
  | Affect (dst, src) -> affect k b dst src
  | Proc (f, es) -> bprintf b "%s(%a)" f (list ", " exp) es
  | Assert e -> bprintf b "assert(%a)" exp e
  | Coproc (e, f, es) ->
      bprintf b "proc.coproc(%a)->%s(%a)" exp e (func f) (list ", " exp) es
  | Block [] -> ()
  | Block (Block _ | For _ | While _ | If _ | Case _ as i :: is) ->
      bprintf b "IntBlock (%a)\n(%a)" (inst_aux k) i (list "" (inst k)) is
  | Block (i :: is) ->
      bprintf b "IntBlock (%a)\n(%a)" (inst_aux k) i (list "\n" (inst k)) is

  | While (e, i) -> bprintf b "while (%a)\n%a" exp e (inst (k+2)) i

  | For (counter, min, max, i) ->
      bprintf b "for (size_t %s = %a; %s<%a; ++%s) \n%a\n"
        counter num min counter num max counter (inst (k+2)) i

  | Case (e, s) ->
      bprintf b "switch (%a) \n%a%a"
        exp e (list "" (case_aux k)) s Genpc.indent k

  | If (e, i1, Some i2) ->
      bprintf b "IntIfElse (%a)\n(%a)\n%a"
	exp e (inst (k)) i1 (*Genpc.indent k*) (inst (k)) i2
  | If (e, i, None) ->
      bprintf b "IntIf (%a)\n(%a)\n"
	exp e (inst (k)) i (*Genpc.indent k*)

  | _ -> string b "TODO7(\"inst\")"

and case_aux k b (n, i) =
  bprintf b "%acase %s:\n%a\n%abreak;\n"
    Genpc.indent k (hex_of_bin n) (inst (k+2)) i Genpc.indent (k+2)

and affect k b dst src =
  if src = Unpredictable_exp then string b "None"
  else
    begin
    match dst with
      | Reg (Var "d", _) -> 
	  bprintf b "Affect_reg d (%a)" exp src
      | Reg (Num n, None) -> bprintf b
	  (*"proc.set_pc_raw(%a)"*) "Affect_reg %s (%a)" (reg_id n) exp src
      | Reg (e, None) -> bprintf b "Affect_reg R%a (%a)" exp e exp src
      | Reg (e, Some m) ->
	  bprintf b "Affect_reg (%a,%s) (%a)" exp e (mode m) exp src
     
      | Var v -> bprintf b "%a = %a" exp (Var v) exp src
      | CPSR -> bprintf b "Affect_cpsr (%a)" exp src
      | SPSR _ as e -> bprintf b "%a = %a" exp e exp src
      | Range (CPSR, Flag (s,_)) ->
          bprintf b "Affect_cpsr_bit %sbit (%a)" s exp src
      | Range (CPSR, Index (Num n)) ->
          bprintf b (*"cpsr.%s = %a"*) "Affect_%s (%a)"
	    (cpsr_flag n) exp src
      | Range (CPSR, Bits (n1, n2)) ->
          bprintf b (*"proc.cpsr.%s = %a"*) "Affect_%s (%a)"
	    (cpsr_field (n1,n2)) exp src
      | Range (e1, Bits (n1, n2)) ->
          inst_aux k b (Proc ("set_field", [e1; Num n1; Num n2; src]))
      | Memory (addr, n) ->
          inst_aux k b (Proc ("proc.mmu.write_" ^ access_type n, [addr; src]))
      | Range (e, Index n) -> inst_aux k b (Proc ("set_bit", [e; n; src]))
      | _ -> string b "TODO9(\"affect\")"
end;;

(** Generate a function modeling an instruction of the processor *)

let version_in_comment b k = bprintf b " (%s)" k;;

let version_in_name b k = bprintf b "_%s" k;;

let prog_var b s = bprintf b "<%s>" s;;

let prog_arg b (v,t) = bprintf b "(%s: %s) " v t;;

let prog_out b (v,t) = bprintf b "%s &%s" t v;;

let local_decl b (v,t) = bprintf b "  %s %s;\n" t v;; 

let ident_in_comment b i =
  bprintf b "%s%a%a" i.iname (list "" prog_var) i.ivars
    (option "" version_in_comment) i.iversion

let ident b i =
  bprintf b "%s%a" i.iname (option "" version_in_name) i.iversion;;

let comment b = function
  | Instruction (r, id, is, _) ->
      bprintf b "// %s %a\n" r (list ", " ident_in_comment) (id :: is)
  | Operand (r, c, n, _) ->
      bprintf b "// %s %a - %a\n" r (list " " string) c (list " " string) n;;

let abbrev b s =
  if s <> "" && 'A' < s.[0] && s.[0] < 'Z'
  then bprintf b "%c" s.[0]
  else bprintf b ""

let arg_sep l l' = match l, l' with _::_, _::_ -> ",\n    " | _ -> "";;

let prog gs ls b p =
  match p with
    | Instruction (_ , id, is, i) ->
        bprintf b "%aDefinition %a %s %a : result :=\n\n%s%a.\n\n" comment p
          (list "_" ident) (id :: is)
	  ("(s : state)\n")
          (list "\n    " prog_arg) gs
          (*(list "" inreg_load) inregs*)
          (*(list "" local_decl) ls*)
	  ("intOp true s\n")
          (inst 0) i
    | Operand (_, c, n, i) ->
        let os = List.filter (fun (x, _) -> not (List.mem x optemps)) ls
        and ls' = List.filter (fun (x, _) -> List.mem x optemps) ls in
          bprintf b "%aDefinition %a_%a(%a%s%a)\n\n%a%a.\n\n" comment p
            (list "" abbrev) c
            (list "_" string) n
            (list "\n    " prog_arg) gs
            (arg_sep gs os)
            (list "\n    " prog_out) os
            (list "" local_decl) ls'
            (inst 2) i;;

(*
let decl gs ls b p = match p with
  | Instruction (_ , id, is, _) ->
      bprintf b "  %a  void %a(%a);\n" comment p
        (list "_" ident) (id :: is) (list ",\n    " prog_arg) gs
  | Operand (_ , c, n, _) ->
      let os = List.filter (fun (x, _) -> not (List.mem x optemps)) ls in
        bprintf b "  %a  void %a_%a(%a%s%a);\n" comment p
          (list "" abbrev) c (list "_" string) n
          (list ",\n    " prog_arg) gs
          (arg_sep gs os)
          (list ",\n    " prog_out) os;;
*)
let lsm_hack p =
  let rec inst = function
    | Block is -> Block (List.map inst is)
    | If (_, Affect ( Reg (Var "n", None), e), None) ->
        Affect (Var "new_Rn", e)
    | i-> i
  in match p with
  | Instruction (r, id, is, i) ->
      if id.iname = "LDM" or id.iname = "STM"
      then (* add 'if (W) then Rn = new_Rn' at the end of the main 'if' *)
        let a = If (Var "W", Affect (Reg (Var "n", None), Var "new_Rn"), None) in
        let i = match i with
          | If (c, Block (is), None) ->
              If (c, Block (is@[a]), None)
          | Block ([x; If (c, Block (is), None)]) ->
              Block ([x; If (c, Block (is@[a]), None)])
          | _ -> raise (Failure ("Unexpected AST shape: "^id.iname))
        in Instruction (r, id, is, i)
      else p
  | Operand (r , c, n, i) ->
      if c = ["Load"; "and"; "Store"; "Multiple"]
      then (* replace 'If (...) then Rn = ...' by 'new_Rn = ...' *)
        Operand (r , c, n, (inst i))
      else p;;

let lib b ps =  
  let b2 = Buffer.create 10000 in
  let no_decl b p = 
    let p' = lsm_hack p in
    let gs, ls = variables p' in
      bprintf b "%a\n" (prog gs ls) p'
  in
    bprintf b "%a%a" (list "" no_decl) ps Buffer.add_buffer b2;;
