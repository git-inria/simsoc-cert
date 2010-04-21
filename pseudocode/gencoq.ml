(**
SimSoC-Cert, a library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Coq code generator based on the Coq library written in ../coq
*)

open Ast;;
open Printf;;
open Util;;

let num = string;;

let bin b s =
  let n = String.length s in
    if n <= 2 || String.sub s 0 2 <> "0b" then invalid_arg "Gencoq.bin";
    bprintf b "%c" s.[2];
    for i = 3 to n-1 do bprintf b "~%c" s.[i] done;;

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

let var = function (*FIXME: to be done in preproc *)
  | "CP15_reg1_EEbit" -> "get_CP15_reg1_EEbit"
  | "CP15_reg1_Ubit" -> "get_CP15_reg1_Ubit"
  | "GE" -> "(cpsr s0)[19#16]"
  | s -> s;;

(***********************************************************************)
(** Coq types of program variables *)
(***********************************************************************)

let type_of_var = function
  | "cond" -> "opcode"
  | "mode" -> "processor_mode"
  | "S" | "L" | "F" | "I" | "A" | "R" | "shifter_carry_out" | "shift" | "mmod"
  | "x" | "y" | "W" | "X" |"U" -> "bool"
  | "n" | "d" | "m" | "s" | "dHi" | "dLo" -> "regnum"
  | "s0" -> "state"
  | "md" -> "processor_mode"
  | "address" -> "address"
  | _ -> "word";;

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

(***********************************************************************)
(** translation of expressions *)
(***********************************************************************)

let input_registers = ["n"; "m"; "s"];;

(*FIXME: to be moved to preproc *)
let optemps = ["index"; "offset_8"; "end_address"];;

let rec pexp b = function
  | Bin _ | Hex _ | Num _ | Var _ as e -> exp b e
  | e -> par exp b e

and exp b = function
  | Bin s -> bin b s
  | Hex s -> bprintf b "w%s" s
  | Num s -> string b s
  | CPSR -> string b "cpsr (proc s0)"
  | Memory (e, n) -> bprintf b "Memory %s %a s0" n exp e
  | Fun (f, es) -> bprintf b "%s %a" (func f) (list " " pexp) es
  | Var s -> string b s
  | If_exp (e1, e2, e3) ->
      bprintf b "if %a then %a else %a" exp e1 exp e2 exp e3

  | SPSR None -> string b "spsr (proc s0) (mode (proc s0))"
  | SPSR (Some m) -> bprintf b "spsr (proc s0) %s" (mode m)

  | BinOp (e1, ("<<" | ">>" | "+" | "-" | "*" | ">=" | "<" | ">" | "Rotate_Right" | "Arithmetic_Shift_Right"  as op), Num n) ->
      exp b (Fun (binop op, [e1; Var (num_word n)]))
  | BinOp (Num n, ("-" | "+" | "*" as op), e2) -> 
      exp b (Fun (binop op, [Var (num_word n); e2]))
  | BinOp (e1, ("Rotate_Right"|"Arithmetic_Shift_Right" | "Logical_Shift_Left"
	   | "Logical_Shift_Right" | "+" | "-" | "*" | "AND" | "OR" | "EOR"
	   | "==" | "!=" | ">=" | "<" | ">>" | "<<" as op), e2) ->
      exp b (Fun (binop op, [e1; e2]))    
  | BinOp (e1, op, Num n) -> bprintf b "%a %s %s" exp e1 (binop op) (num_word n)
  | BinOp (e1, op, e2) -> bprintf b "(%a) %s (%a)" exp e1 (binop op) exp e2

  | Reg (Var s, None) -> bprintf b "reg_content (proc s0) %s" s
  | Reg (Num n, None) -> bprintf b "reg_content (proc s0) %s" (reg_id n)
  | Reg (e, None) -> bprintf b "reg_content (proc s0) R%a" exp e
  | Reg (e, Some m) ->
      bprintf b "reg (proc s0) (reg_of_mode %a %s)" exp e (mode m)

  | Range (CPSR, Flag (s,_)) -> bprintf b "(cpsr s0)[%sbit]" s
  | Range (e1, Index e2) -> bprintf b "(%a)[%a]" exp e1 exp e2
  | Range (e, Bits (n1, n2)) -> bprintf b "%a[%s#%s]" pexp e n1 n2

  | _ -> string b "TODO6";;

(***********************************************************************)
(** translation of instructions *)
(***********************************************************************)

let rec inst k b = function
  | Block _ | For _ | While _ | If _ | Case _ as i ->
      bprintf b "%a" (*Genpc.indent (k)*) (inst_aux k) i
  | i -> bprintf b "%a" (*Genpc.indent (k)*) (inst_aux k) i

and inst_aux k b = function
  | Unpredictable -> string b "unpredictable \"\"" (*FIXME*)

  | Affect (dst, src) -> affect k b dst src
  | Proc (f, es) -> bprintf b "%s%a" f (list " " pexp) es
  | Assert e -> bprintf b "assert(%a)" exp e
  | Coproc (e, f, es) ->
      bprintf b "proc.coproc(%a)->%s(%a)" exp e (func f) (list " " exp) es

  | Block [] -> () 
  | Block (Block _ | For _ | While _ | If _ | Case _ as i :: is) ->
      bprintf b "block(\n%a%a::\n%anil)" Genpc.indent (k+2) 
	(inst_aux k) i (list "\n" (block_aux k)) is
  | Block (is) ->
      bprintf b "block(\n%anil)"
	(list "\n" (block_aux k)) is

  | While (e, i) -> bprintf b "while (%a)\n%a" exp e (inst (k+2)) i

  | For (counter, min, max, i) ->
      bprintf b "for (size_t %s = %a; %s<%a; ++%s) \n%a\n"
        counter num min counter num max counter (inst (k+2)) i

  | Case (e, s) ->
      bprintf b "switch (%a) \n%a%a"
        exp e (list "" (case_aux k)) s Genpc.indent k

  | If (e, i1, Some i2) ->
      bprintf b "if_then_else (%a)\n  %a(%a)\n  %a(%a)"
	exp e Genpc.indent (k+2) (inst (k+2)) i1
	Genpc.indent (k+2) (inst (k+2)) i2

  | If (e, i, None) ->
      bprintf b "if_then (%a)\n%a(%a)"
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
      | _ -> string b "TODO9(\"affect\")";;

(***********************************************************************)
(** semantic step function of some instruction *)
(***********************************************************************)

let version_in_comment b k = bprintf b " (%s)" k;;

let version_in_name b k = bprintf b "_%s" k;;

let prog_var b s = bprintf b "<%s>" s;;

let prog_arg b (v,t) = bprintf b "(%s : %s) " v t;;

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
        bprintf b "%aDefinition %a_step %s %a: result :=\n%a%s.\n" comment p
          (list "_" ident) (id :: is)
	  "(s0 : state)"
          (list "" prog_arg) gs
	  (*(list "" local_decl) ls*)
          (inst 2) i
	  ("\n  true s0")
    | Operand (_, c, n, i) ->
        let os = List.filter (fun (x, _) -> not (List.mem x optemps)) ls
        and ls' = List.filter (fun (x, _) -> List.mem x optemps) ls in
          bprintf b "%aDefinition %a_%a(%a%s%a)\n%a%a.\n" comment p
            (list "" abbrev) c
            (list "_" string) n
            (list "" prog_arg) gs
            (arg_sep gs os)
            (list "" prog_out) os
            (list "" local_decl) ls'
            (inst 2) i;;

let lsm_hack p =
  let rec inst = function
    | Block is -> Block (List.map inst is)
    | If (_, Affect (Reg (Var "n", None), e), None) -> Affect (Var "new_Rn", e)
    | i -> i
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

(***********************************************************************)
(** constructor of some instruction *)
(***********************************************************************)

let inst_typ gs b = function
  | Operand _ -> ()
  | Instruction (_ , id, ids, _) ->
      bprintf b "| %a %a" (list "_" ident) (id :: ids) (list "" prog_arg) gs;;

(***********************************************************************)
(** call to the semantics step function of some instruction *)
(***********************************************************************)

let var_name b (v, _) = bprintf b "%s" v;;

let name = list "_" ident;;

let inst_sem gs b = function
  | Operand _ -> () (*FIXME*)
  | Instruction (_, id, ids, _) ->
      bprintf b "    | %a %a =>" name (id::ids) (list " " var_name) gs;
      if List.exists ((=) ("shifter_operand", "word")) gs then
	bprintf b "\n      let (v, _) := shifter_operand_value_and_carry s0 w shifter_operand in\n       ";
      bprintf b " %a_step %a v s0" name (id::ids) (list " " var_name) gs;;

(***********************************************************************)
(** Main coq generation function.
For each instruction:
- generate its semantics step function
- generate the corresponding constructor for the type of instructions
- generate the call to its semantics step function in the general
semantics step function *)
(***********************************************************************)

let lib b ps =
  let btyp = Buffer.create 10000 in
  let bsem = Buffer.create 10000 in
  let prog_typ_sem p =
    let p = lsm_hack p in
    let gs, ls = variables p in
      bprintf b "%a\n" (prog gs ls) p;
      bprintf btyp "%a\n" (inst_typ gs) p;
      bprintf bsem "%a\n" (inst_sem gs) p
  in
    bprintf b "Require Import Bitvec List Semantics Integers Util Functions Config Proc State.\n";
    bprintf b "Import Int.\n\n";
    List.iter prog_typ_sem ps;
    bprintf b "Inductive instruction : Type :=\n";
    Buffer.add_buffer b btyp;
    bprintf b "\nDefinition execute (w : word) (i : instruction) (s0 : state) : result :=\n  match i with\n";
    Buffer.add_buffer b bsem;;
