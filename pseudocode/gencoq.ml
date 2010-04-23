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

let comment f b x = bprintf b "(*%a*)" f x;;

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
(** variable types *)
(***********************************************************************)

let type_of_var = function
  | "cond" -> "opcode"
  | "S" | "L" | "F" | "I" | "A" | "R" | "shifter_carry_out" | "shift" | "mmod"
  | "x" | "y" | "W" | "X" |"U" -> "bool"
  | "n" | "d" | "m" | "s" | "dHi" | "dLo" -> "regnum"
  | "s0" -> "state"
  | "md" | "mode" -> "proc_mode"
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
(** numbers *)
(***********************************************************************)

let num = string;;

let bin b s =
  let n = String.length s in
    if n <= 2 || String.sub s 0 2 <> "0b" then invalid_arg "Gencoq.bin";
    let i = ref 2 in
      while s.[!i] = '0' && !i < n do incr i done;
      if !i >= n then string b "Z0"
      else begin
	string b "Zpos 1";
	for i = !i+1 to n-1 do bprintf b "~%c" s.[i] done
      end;;

let bin b s = par bin b s;;

(*IMPROVE: use a Coq function to convert an hexa string into a word? *)
let hex b s =
  comment string b s;
  (*FIXME: there is a problem here with scanf *)
  let n = Scanf.sscanf s "%lX" (fun x -> x) in
    if Int32.compare n Int32.zero <= 0 then bprintf b "Z0"
    else bprintf b "Zpos %lX" n;;

let hex b s = par hex b s;;

let word f b s = bprintf b "repr %a" f s;;

(***********************************************************************)
(** registers *)
(***********************************************************************)

let coq_regnum = function
  | "15" -> "PC"
  | "14" -> "LR"
  | "13" -> "SP"
  | s -> Printf.sprintf "(mk_regnum %s)" s;;

let regnum b s = string b (coq_regnum s);;

(***********************************************************************)
(** modes *)
(***********************************************************************)

let exn_mode = Genpc.mode;;

let string_of_mode = function
  | Usr -> "usr"
  | Sys -> "sys"
  | m -> "(exn " ^ Genpc.string_of_mode m ^ ")";;

let mode b m = string b (string_of_mode m);;

(***********************************************************************)
(** functions *)
(***********************************************************************)
 
let coq_fun_name = function
  | "address_of_the_instruction_after_the_branch_instruction"
  | "address_of_instruction_after_the_BLX_instruction"
  | "address_of_the_instruction_after_the_BLX_instruction"
  | "address_of_next_instruction_after_the_SWI_instruction"
    -> "next_inst_address s0"
  | "address_of_BKPT_instruction" -> "cur_inst_address s0"
  | "CurrentModeHasSPSR" -> "CurrentModeHasSPSR s0"
  | "InAPrivilegedMode" -> "InAPrivilegedMode s0"
  | "ConditionPassed" -> "ConditionPassed s0"
  | "SignExtend_30" -> "SignExtend_24to30" (*FIXME*)
  | "NOT" -> "not"
  | "not" -> "negb"
  | "AND" -> "and"
  | "OR" -> "or"
  | "EOR" -> "xor"
  | "and" -> "andb"
  | "or" -> "orb"
  | "+" -> "add"
  | "-" -> "sub"
  | "*" -> "mul"
  | "==" -> "zeq"
  | "!=" -> "zne"
  | ">=" -> "zge"
  | "<" -> "zlt"
  | "<<" -> "Logical_Shift_Left"
  | s -> s;;

let fun_name b s = string b (coq_fun_name s);;

(***********************************************************************)
(** expressions *)
(***********************************************************************)

(*REMOVE when finished! *)
let todo f b e = bprintf b "todo \"%a\"" f e;;

let rec pexp b = function
  | Var _ as e -> exp b e
  | e -> par exp b e

and pexp_num b = function
  | Num s -> num b s
  | e -> pexp b e

and pexp_regnum b = function
  | Num s -> regnum b s
  | e -> pexp b e

and exp b = function
  | Bin s -> word bin b s
  | Hex s -> word hex b s
  | Num s -> word num b s
  | Var s -> string b s
  | Fun (f, []) -> fun_name b f
  | Fun (f, es) -> bprintf b "%a %a" fun_name f (list " " pexp) es
  | BinOp (e1, ("==" as f), Num n) ->
      bprintf b "%a %a %a" fun_name f pexp e1 num n
  | BinOp (e1, f, e2) -> bprintf b "%a %a %a" fun_name f pexp e1 pexp e2
  | If_exp (e1, e2, e3) ->
      bprintf b "if %a then %a else %a" exp e1 exp e2 exp e3
  | CPSR -> string b "cpsr s0"
  | Range (e, r) -> bprintf b "%a[%a]" pexp e range r

  | SPSR None -> string b "spsr s0 None"
  | SPSR (Some m) -> bprintf b "spsr s0 (Some %a)" exn_mode m

  | Reg (e, None) -> bprintf b "reg_content s0 %a" pexp_regnum e
  | Reg (e, Some m) ->
      bprintf b "reg_content_of_mode s0 %a %a" pexp_regnum e mode m

  | Memory (_, _) as e -> todo Genpc.exp b e
  | Coproc_exp (_, _, _) as e -> todo Genpc.exp b e

  | Other _ | Unpredictable_exp | Unaffected -> invalid_arg "Gencoq.exp"

and range b = function
  | Flag (s, _) -> bprintf b "%sbit" s
  | Index e -> pexp_num b e
  | Bits (n1, n2) -> bprintf b "%a#%a" num n1 num n2;;

(***********************************************************************)
(** instructions *)
(***********************************************************************)

let rec inst k b i = indent b k; inst_aux k b i

and pinst k b i = indent b k; par (inst_aux k) b i

and cons k b i = indent b k; postfix " ::" (inst_aux k) b i

and inst_aux k b = function
  | Unpredictable -> string b "unpredictable \"\"" (*FIXME*)
  | Proc (f, es) -> bprintf b "%a %a" fun_name f (list " " pexp) es
  | Block is ->
      bprintf b "block (\n%a\n%anil)" (list "\n" (cons (k+2))) is indent (k+2)
  | If (e, i, None) -> bprintf b "if_then %a\n%a" pexp e (pinst (k+2)) i
  | If (e, i1, Some i2) ->
      bprintf b "if_then_else %a\n%a\n%a"
	pexp e (pinst (k+2)) i1 (pinst (k+2)) i2
  | Affect (e1, e2) as i ->
      begin try bprintf b "%a %a" affect e1 pexp e2
      with Not_found -> todo (Genpc.inst 0) b i end
  | While _ | For _ | Coproc _ | Case _ as i -> todo (Genpc.inst 0) b i
  | Misc _ | Assert _ -> invalid_arg "Gencoq.inst"

and affect b = function
  | Reg (e, None) -> bprintf b "set_reg %a" pexp_regnum e
  | Reg (e, Some m) -> bprintf b "set_reg_mode %a %a" mode m pexp_regnum e
  | CPSR -> bprintf b "set_cpsr"
  | SPSR None -> bprintf b "set_spsr None"
  | SPSR (Some m) -> bprintf b "set_spsr (Some %a)" exn_mode m
  | Range (CPSR, Flag (s, _)) -> bprintf b "set_cpsr_bit %sbit" s
  | Range (CPSR, Bits (n, p)) -> bprintf b "set_cpsr_bits %a %a" num n num p
  | _ -> raise Not_found;;

(*    match dst with
      | Reg (Num n, None) ->
	  bprintf b "set_reg %a (%a)" regnum n exp src
 
      | Reg (e, None) ->
	  begin match src with
	    | Num n -> bprintf b "set_reg %a %s" exp e (num_word n)
	    | _ -> bprintf b "set_reg %a (%a)" exp e exp src
	  end

      | Reg (Num n, Some m) ->
	  bprintf b "set_reg_of_mode %a (%a) %a" 
	    regnum n exp src mode m
      | Var "address" -> bprintf b "address_of_word (%a)" exp src
      | Var v -> bprintf b 
	  "let %a := %a in" exp (Var v) exp src
      | CPSR -> bprintf b "set_cpsr (%a)" exp src
      | SPSR (Some m)  -> bprintf b "set_spsr (%a) (Some %a)" 
	  exp src mode m
      | SPSR None -> bprintf b "set_spsr (%a) None" exp src
      | Range (CPSR, Flag (s,_)) ->
	  begin match src with
	    | Num n -> bprintf b "set_cpsr_bit %sbit (%s) (cpsr s0)" 
		s (num_word n)
	    | _ -> bprintf b "set_cpsr_bit %sbit (%a) (cpsr s0)" 
		s exp src
	  end
      | Range (CPSR, Index (Num n)) ->
          bprintf b "set_cpsr_bit %s (%a) (cpsr s0)"
	    (cpsr_flag n) exp src
      | Range (Var ("accvalue" as v), Bits (("31" as n1), ("0" as n2)))
	-> bprintf b "let %a := w0 in let %a := %a in"
	  exp (Var v) exp (Var v) 
	    (inst k) (Proc ("update_bits ",
			    [Num n1; Num n2; src; Var v]))
      | Range (e1, Bits (n1, n2)) ->
	  begin match e1 with
	    | Var ("GE" as v) ->
		bprintf b "set_cpsr (%a)"
		  (inst k) (Proc ("update_bits ",
				  [Num n1; Num n2; src; Var v]))
	    | Var v ->
		bprintf b "let %a := %a in" 
		  exp (Var v)
		  (inst k) (Proc ("update_bits ", 
				  [Num n1; Num n2; src; Var v]))
	    | Reg (e, _) ->
		bprintf b "set_reg %a (%a)" exp e
		  (inst k) (Proc ("update_bits ",
				  [Num n1; Num n2; src; e]))
	    | CPSR ->
		bprintf b "set_cpsr_bits %s %s (mode_number (%a)) (cpsr s0)" 
		  n1 n2 exp src
	    | _ ->
		inst k b (Proc ("update_bits ",
				    [Num n1; Num n2; src; e1]))
	  end
      | Memory (addr, n) ->
          inst k b (Proc ("update_mem" ^ access_type n, [addr; src]))
      | Range (e, Index n) ->
	  begin match e with
	    | Var ("GE" as v) ->
		bprintf b "set_cpsr (%a)"
		  (inst k) (Proc ("update_bit ", [n; src; Var v]))
	    | _ ->
		inst k b (Proc ("update_bit ", [n; src; e]))
	  end

      | Coproc_exp (_, _, _) | Other _ | BinOp (_, _, _) | Fun (_, _)
      | If_exp (_, _, _) | Hex _ | Bin _ | Num _ | Unpredictable_exp
      | Unaffected | Reg (_, _) | Range (_, _) ->
	  bprintf b "TODO: %a" (Genpc.inst 0) (Affect (dst, src))*)

(***********************************************************************)
(** semantic step function of some instruction *)
(***********************************************************************)

let ident b i =
  bprintf b "%s%a%a" i.iname (list "" string) i.iparams
    (option "" string) i.iversion;;

let prog_name = list "_" ident;;

let prog_arg b (v, t) = bprintf b "(%s : %s)" v t;;

let prog gs _ls b p =
  match p with
    | Instruction (_ , id, ids, i) ->
        bprintf b
"(* %a *)\nDefinition %a_step (s0 : state) %a: result :=\n%a true s0.\n"
	  Genpc.prog_name p
          prog_name (id::ids)
          (list " " prog_arg) gs
          (inst 2) i
    | Operand (_, _c, _n, _i) -> () (*FIXME*);;

let lsm_hack p =
  let rec inst = function
    | Block is -> Block (List.map inst is)
    | If (_, Affect (Reg (Var "n", None), e), None) -> Affect (Var "new_Rn", e)
    | i -> i
  in match p with
  | Instruction (r, id, is, i) ->
      if id.iname = "LDM" or id.iname = "STM"
      then (* add 'if (W) then Rn = new_Rn' at the end of the main 'if' *)
        let a = If (Var "W", Affect (Reg (Var "n", None), Var "n"), None) in
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
  | Operand _ -> () (*FIXME*)
  | Instruction (_ , id, ids, _) ->
      bprintf b "| %a %a" prog_name (id::ids) (list " " prog_arg) gs;;

(***********************************************************************)
(** call to the semantics step function of some instruction *)
(***********************************************************************)

let var_name b (v, _) = bprintf b "%s" v;;

let inst_sem gs b = function
  | Operand _ -> () (*FIXME*)
  | Instruction (_, id, ids, _) ->
      bprintf b "    | %a %a =>" prog_name (id::ids) (list " " var_name) gs;
      if List.exists ((=) ("shifter_operand", "word")) gs then
	if List.exists ((=) ("shifter_carry_out", "bool")) gs then 
	  bprintf b "\n      let (v, shifter_carry_out) := shifter_operand_value_and_carry s0 w shifter_operand in\n       "
	else
	bprintf b "\n      let (v, _) := shifter_operand_value_and_carry s0 w shifter_operand in\n       ";
      bprintf b " %a_step %a v s0" prog_name (id::ids) (list " " var_name) gs;;

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
    bprintf b "Require Import Bitvec List Integers Util Functions Config Arm State Semantics.\nRequire Import ZArith.\nImport Int.\n\nModule Inst (Import C : CONFIG).\n\n";
    List.iter prog_typ_sem ps;
    bprintf b "Inductive instruction : Type :=\n";
    Buffer.add_buffer b btyp;
    bprintf b "\nDefinition execute (w : word) (i : instruction) (s0 : state) : result :=\n  match i with\n";
    Buffer.add_buffer b bsem;;
