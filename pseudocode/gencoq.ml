
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
  | "0b10111" -> "exn abt"
  | "0b10011" -> "exn svc"
  | "0b10000" -> "exn usr"
  | "0b10001" -> "exn fiq"
  | "0b10010" -> "exn irq"
  | "0b11011" -> "und"
  | "0b11111" -> "sys"
  | _ -> "TODO0";;

let hex = function
  | "0x000000ff" -> "0x000000FF"
  | "0x00ff00ff" -> "0x00FF00FF"
  | "0x0000ffff" -> "0x0000FFFF"
  | s -> s;;

(*coq types of usual var*)

let type_of_var = function
  | "cond" -> "opcode"
  | "mode" -> "processor_mode"
  | "S" | "L" | "F" | "I" | "A" | "R" | "shifter_carry_out" | "shift" | "mmod"
  | "x" | "y" | "W" | "X" |"U"
      -> "bool"
  | "shifter_operand" | "shift_imm" | "immed_8" | "signed_immed_24" | "H"
  | "imod" | "sat_imm" | "start_address" | "new_Rn" |"opcode" | "cp_num"
  | "register_list" | "field_mask" | "rotate_imm" | "rotate" | "offset_12"
  | "index" | "immedL" | "immedH" | "offset_8" | "end_address"
      -> "word"
  | "n" | "d" | "m" | "s" | "dHi" | "dLo" -> "reg_num"
  | "s0" -> "state"
  | "md" -> "processor_mode"
  | "address" -> "address"
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
  | "3" -> "w3"
  | "4" -> "w4"
  | "8" -> "w8"
  | "16" -> "w16"
  | "31" -> "w31"
  | "32" -> "w32"
  | _ -> "TODO0";;

let cpsr_flag = function
  | "31" -> "N_flag"
  | "30" -> "Z_flag"
  | "29" -> "C_flag"
  | "28" -> "V_flag"
  | "27" -> "Q_flag"
  | "24" -> "J_flag"
  | "9" -> "Ebit"
  | "8" -> "Abit"
  | "7" -> "Ibit"
  | "6" -> "Fbit"
  | "5" -> "Tbit"
  | _ -> "TODO2";;

let reg_id = function
  | "15" -> "PC"
  | "14" -> "LR"
  | "13" -> "SP"
  | n -> n;;

let func = function
  | "address_of_the_instruction_after_the_branch_instruction"
  | "address_of_instruction_after_the_BLX_instruction"
  | "address_of_the_instruction_after_the_BLX_instruction"
  | "address_of_next_instruction_after_the_SWI_instruction"
    -> "next_inst_address s0"
  | "address_of_BKPT_instruction" -> "cur_inst_address s0"
  | "ConditionPassed" -> "ConditionPassed (cpsr s0)"
  | "CurrentModeHasSPSR" -> "CurrentModeHasSPSR s0"
  | "SignExtend_30" -> "SignExtend_24to30"
  | "InAPrivilegedMode" -> "InAPrivilegedMode s0"
  | "NOT" -> "not"
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
  | "<" -> "zlt"
  | "Logical_Shift_Left" -> "Logical_Shift_Left"
  | "<<" -> "Logical_Shift_Left"
  | "Logical_Shift_Right"| ">>" -> "Logical_Shift_Right"
  | "Arithmetic_Shift_Right" -> "Arithmetic_Shift_Right"
  | "Rotate_Right" -> "Rotate_Right"
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
  | "CP15_reg1_EEbit" -> "get_CP15_reg1_EEbit"
  | "CP15_reg1_Ubit" -> "get_CP15_reg1_Ubit"
  | "PrivMask" -> "PrivMask"
  | "UserMask" -> "UserMask"
  | "StateMask" -> "StateMask"
  | "UnallocMask" -> "UnallocMask"
  | "GE" -> "(cpsr s0)[19#16]"
  | "v5_and_above" -> "proc.v5_and_above"
  | s -> s;;

let input_registers = ["n"; "m"; "s"];;

let optemps = ["index"; "offset_8"; "end_address"];;

let rec exp b = function
  | Bin s -> string b (hex_of_bin s)
  (*| Hex s -> bprintf b "w%s" s*)
  | Hex s -> bprintf b "w%s" (hex s)
  | Num s -> string b s
  | CPSR -> string b "cpsr s0"
  | SPSR None -> string b "spsr s0 None"
  | SPSR (Some m) -> bprintf b "spsr s0 Some(%s)" (mode m)
  | Memory (e, n) -> bprintf b "Memory %s %a s0" n exp e
  | BinOp (e1, ("<<" | ">>" | "+" | "-" | "*" | ">=" | "<" | ">" | "Rotate_Right"
	   | "Arithmetic_Shift_Right"  as op), Num n) ->
      exp b (Fun (binop op, [e1; Var (num_word n)]))
  | BinOp (Num n, ("-" | "+" | "*" as op), e2) -> 
      exp b (Fun (binop op, [Var (num_word n); e2]))
  | BinOp (e1, ("Rotate_Right"|"Arithmetic_Shift_Right" | "Logical_Shift_Left"
	   | "Logical_Shift_Right" | "+" | "-" | "*" | "AND" | "OR" | "EOR"
	   | "==" | "!=" | ">=" | "<" | ">>" | "<<" as op), e2) ->
      exp b (Fun (binop op, [e1; e2]))    

  | BinOp (e1, op, Num n) -> bprintf b "%a %s %s" exp e1 (binop op) (num_word n)
  | BinOp (e1, op, e2) -> bprintf b "(%a) %s (%a)" exp e1 (binop op) exp e2
  | Fun (f, es) -> 
	bprintf b "%s %a" (func f) (list " " para) es

  | If_exp (e1, e2, e3) ->
      begin match e2, e3 with
	| Num n2, Num n3 -> bprintf b "if (%a) then %s else %s"
	    exp e1 (num_word n2) (num_word n3)
	| Bin n2, Num n3 -> bprintf b "if (%a) then %s else %s"
	    exp e1 (num_word (hex_of_bin n2)) (num_word n3)
	| Hex n2, Num n3 -> bprintf b "if (%a) then w%s else %s"
	    exp e1 n2 (num_word n3)
	| Num n2, Bin n3 -> bprintf b "if (%a) then %s else %s"
	    exp e1 (num_word n2) (num_word (hex_of_bin n3))
	| _ -> bprintf b "if (%a) then %a else %a" 
	    exp e1 exp e2 exp e3
      end
  | Reg (Var s, None) ->
      (*if List.mem s input_registers
      then bprintf b "reg_content s0 %s" s
      else*) bprintf b "reg_content s0 %s" s
  | Reg (Num n, None) -> bprintf b "reg_content s0 %s" (reg_id n)
  | Reg (e, None) -> bprintf b "reg_content s0 R%a" exp e
  | Reg (e, Some m) -> bprintf b "reg s0 (reg_of_mode %a %s)"
      exp e (mode m)
  | Range (CPSR, Flag (s,_)) -> bprintf b "(cpsr s0)[%sbit]" s
  | Range (e1, Index e2) -> bprintf b "(%a)[%a]" exp e1 exp e2
  | Range (e, Bits (n1, n2)) ->
      begin match n1, n2 with
        | "15", "0" -> bprintf b "(%a)[15#0]" exp e
        | "31", "16" -> bprintf b "(%a)[31#16]" exp e
        | "7", "0" -> bprintf b "(%a)[7#0]" exp e
        | "15", "8" -> bprintf b "(%a)[15#8]" exp e
        | "23", "16" -> bprintf b "(%a)[23#16]" exp e
        | "31", "24" -> bprintf b "(%a)[31#24]" exp e
        | _ -> bprintf b "(%a)[%s#%s]" exp e n1 n2
      end
  | Coproc_exp (e, f, es) ->
      bprintf b "proc.coproc(%a)->%s(%a)" exp e (func f) (list ", " exp) es
  | Var str -> string b (var str)

  | _ -> string b "TODO6"

and para b e =
  begin match e with
    | Bin _ | Hex _ | Num _ | Var _ -> bprintf b "%a" exp e
    | _ -> bprintf b "(%a)" exp e
  end
;;

let rec inst k b = function
  | Block _ | For _ | While _ | If _ | Case _ as i ->
      bprintf b "%a" (*Genpc.indent (k)*) (inst_aux k) i
  | i -> bprintf b "%a" (*Genpc.indent (k)*) (inst_aux k) i

and inst_aux k b = function
  | Unpredictable -> string b "unpredictable"

  | Affect (dst, src) -> affect k b dst src
  | Proc (f, es) -> bprintf b "%s%a" f (list " " para) es
  | Assert e -> bprintf b "assert(%a)" exp e
  | Coproc (e, f, es) ->
      bprintf b "proc.coproc(%a)->%s(%a)" exp e (func f) (list " " exp) es
  | Block [] -> () 

  | Block (Block _ | For _ | While _ | If _ | Case _ as i :: is) ->
      bprintf b "intBlock(\n%a%a::\n%anil)" Genpc.indent (k+2) 
	(inst_aux k) i (list "\n" (block_aux k)) is
  | Block (is) ->
      bprintf b "intBlock(\n%anil)"
	(list "\n" (block_aux k)) is

  | While (e, i) -> bprintf b "while (%a)\n%a" exp e (inst (k+2)) i

  | For (counter, min, max, i) ->
      bprintf b "for (size_t %s = %a; %s<%a; ++%s) \n%a\n"
        counter num min counter num max counter (inst (k+2)) i

  | Case (e, s) ->
      bprintf b "switch (%a) \n%a%a"
        exp e (list "" (case_aux k)) s Genpc.indent k

  | If (e, i1, Some i2) ->
      bprintf b "intIfElse (%a)\n  %a(%a)\n  %a(%a)"
	exp e Genpc.indent (k+2) (inst (k+2)) i1
	Genpc.indent (k+2) (inst (k+2)) i2

  | If (e, i, None) ->
      bprintf b "intIf (%a)\n%a(%a)"
	exp e Genpc.indent (k+2) (inst (k+2)) i

  | _ -> string b "TODO7(\"inst\")"

and block_aux k b i =
  match i with
    | Affect (Var _, _) | If (_, Affect (Var _, _),  _)
    | Affect (Range (Var "accvalue", Bits _), _) ->
	bprintf b "%a%a" Genpc.indent (k+2) (inst (k+2)) i
    | _ -> 
	bprintf b "%a%a::" Genpc.indent (k+2) (inst (k+2)) i 

and case_aux k b (n, i) =
  bprintf b "%acase %s:\n%a\n%abreak;\n"
    Genpc.indent k (hex_of_bin n) (inst (k+2)) i Genpc.indent k

and affect k b dst src =
  if src = Unpredictable_exp then string b "unpredictable"
  else
    begin
    match dst with
      | Reg (Num n, None) ->
	  bprintf b "affect_reg %s (%a)" (reg_id n) exp src
 
      | Reg (e, None) ->
	  begin match src with
	    | Num n -> bprintf b "affect_reg %a %s" exp e (num_word n)
	    | _ -> bprintf b "affect_reg %a (%a)" exp e exp src
	  end

      | Reg (Num n, Some m) ->
	  bprintf b "affect_reg_of_mode %s (%a) %s" 
	    (reg_id n) exp src (mode m)
      | Var "address" -> bprintf b "address_of_word (%a)" exp src
      | Var v -> bprintf b 
	  "let %a := %a in" exp (Var v) exp src
      | CPSR -> bprintf b "affect_cpsr (%a)" exp src
      | SPSR (Some m)  -> bprintf b "affect_spsr (%a) (Some %s)" 
	  exp src (mode m)
      | SPSR None -> bprintf b "affect_spsr (%a) None" exp src
      | Range (CPSR, Flag (s,_)) ->
	  begin match src with
	    | Num n -> bprintf b "affect_cpsr_bit %sbit (%s) (cpsr s0)" 
		s (num_word n)
	    | _ -> bprintf b "affect_cpsr_bit %sbit (%a) (cpsr s0)" 
		s exp src
	  end
      | Range (CPSR, Index (Num n)) ->
          bprintf b "affect_cpsr_bit %s (%a) (cpsr s0)"
	    (cpsr_flag n) exp src
      | Range (Var ("accvalue" as v), Bits (("31" as n1), ("0" as n2)))
	-> bprintf b "let %a := w0 in let %a := %a in"
	  exp (Var v) exp (Var v) 
	    (inst k) (Proc ("update_bits ",
			    [Num n1; Num n2; src; Var v]))
      | Range (e1, Bits (n1, n2)) ->
	  begin match e1 with
	    | Var ("GE" as v) ->
		bprintf b "affect_cpsr (%a)"
		  (inst k) (Proc ("update_bits ",
				  [Num n1; Num n2; src; Var v]))
	    | Var v ->
		bprintf b "let %a := %a in" 
		  exp (Var v)
		  (inst k) (Proc ("update_bits ", 
				  [Num n1; Num n2; src; Var v]))
	    | Reg (e, _) ->
		bprintf b "affect_reg %a (%a)" exp e
		  (inst k) (Proc ("update_bits ",
				  [Num n1; Num n2; src; e]))
	    | CPSR ->
		bprintf b "affect_cpsr_bits %s %s (mode_number (%a)) (cpsr s0)" 
		  n1 n2 exp src
	    | _ ->
		inst_aux k b (Proc ("update_bits ",
				    [Num n1; Num n2; src; e1]))
	  end
      | Memory (addr, n) ->
          inst_aux k b (Proc ("update_mem" ^ access_type n, [addr; src]))
      | Range (e, Index n) ->
	  begin match e with
	    | Var ("GE" as v) ->
		bprintf b "affect_cpsr (%a)"
		  (inst k) (Proc ("update_bit ", [n; src; Var v]))
	    | _ ->
		inst_aux k b (Proc ("update_bit ", [n; src; e]))
	  end
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
  bprintf b "%s%a%a" i.iname
    (list "" string) i.ivars
    (option "" version_in_name) i.iversion;;

let comment b = function
  | Instruction (r, id, is, _) ->
      bprintf b "(* %s %a *)\n" r (list ", " ident_in_comment) (id :: is)
  | Operand (r, c, n, _) ->
      bprintf b "(* %s %a - %a *)\n" r (list " " string) c (list " " string) n;;

let abbrev b s =
  if s <> "" && 'A' < s.[0] && s.[0] < 'Z'
  then bprintf b "%c" s.[0]
  else bprintf b ""

let arg_sep l l' = match l, l' with _::_, _::_ -> ",\n    " | _ -> "";;

let prog gs ls b p =
  match p with
    | Instruction (_ , id, is, i) ->
        bprintf b "%aDefinition %a %s %a : result :=\n\n%a%s.\n\n" comment p
          (list "_" ident) (id :: is)
	  ("(s0 : state)\n")
          (list "\n    " prog_arg) gs
	  (*(list "" local_decl) ls*)
          (inst 2) i
	  ("\ntrue s0")
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
        let a = If (Var "W", Affect (Reg (Var "n", None), 
				     Var "reg_content n s"), None) in
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


let instr_type gs b p =
  match p with
    | Instruction (_ , id, is, _) ->
	bprintf b "|%a_i %a\n"
          (list "_" ident) (id :: is) (list "" prog_arg) gs
    | Operand _ ->
	string b "";;

let args b (v,_) = bprintf b "%s " v;;

let execute gs b p = 
  match p with
    | Instruction (_, id, is, _) ->
	if (List.exists ((=) ("shifter_operand", "word")) gs) then
	  bprintf b
	    "    |%a_i %a =>
      let (v, _) := shifter_operand_value_and_carry s0 w shifter_operand in
      %a %a v s0"
	    (list "_" ident) (id :: is) (list "" args) gs 
	    (list "_" ident) (id :: is) (list "" args) gs
	else 
	  bprintf b 
	    "    |%a_i %a =>
      %a %a s0"
	    (list "_" ident) (id :: is) (list "" args) gs
	    (list "_" ident) (id :: is) (list "" args) gs
    | Operand _ -> string b "";;

let lib b ps =
  let b2 = Buffer.create 10000 in
  let b3 = Buffer.create 10000 in
  let prog_type_exe b p =
    let p' = lsm_hack p in
    let gs, ls = variables p' in
      bprintf b "%a\n" (prog gs ls) p';
      bprintf b2 "%a\n" (instr_type gs) p'
      ;bprintf b3 "%a\n" (execute gs) p'
  in
    bprintf b
      "%aInductive instruction : Type :=\n%a
Definition execute (w : word) (i : instruction)
  (s0 : state) : result := 
  match i with\n%a"
      (list "" prog_type_exe) ps Buffer.add_buffer b2 
      Buffer.add_buffer b3;;
