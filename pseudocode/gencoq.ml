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

(***********************************************************************)
(** variable types *)
(***********************************************************************)

let type_of_var = function
  | "cond" -> "opcode"
  | "shifter_carry_out" | "shift" | "mmod" | "opcode25" -> "bool"
  | "n" | "d" | "m" | "s" | "dHi" | "dLo" -> "regnum"
  | "address" | "start_address" -> "address"
  | s -> if String.length s = 1 then "bool" else "word";;

module G = struct

  type typ = string;;

  let global_type = type_of_var;;

  let type_of_size = function
    | Byte -> "byte"
    | Half -> "half"
    | Word -> "word";;

  let local_type s e =
    match e with
      | Memory (_, n) -> type_of_size n
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
  let n = Scanf.sscanf s "%li" (fun x -> x) in
    if Int32.compare n Int32.zero = 0 then bprintf b "Z0"
    else bprintf b "Zpos %lu" n;;

let hex b s = par hex b s;;

let word f b s = bprintf b "repr %a" f s;;

(***********************************************************************)
(** registers *)
(***********************************************************************)

let string_of_regnum = function
  | "15" -> "PC"
  | "14" -> "LR"
  | "13" -> "SP"
  | s -> Printf.sprintf "(mk_regnum %s)" s;;

let regnum b s = string b (string_of_regnum s);;

(***********************************************************************)
(** memory size *)
(***********************************************************************)

let string_of_size = function
  | Byte -> "Byte"
  | Half -> "Half"
  | Word -> "Word";;

let size b s = string b (string_of_size s);;

(***********************************************************************)
(** processor modes *)
(***********************************************************************)

let exn_mode = Genpc.mode;;

let string_of_mode = function
  | Usr -> "usr"
  | Sys -> "sys"
  | m -> "(exn " ^ Genpc.string_of_mode m ^ ")";;

let mode b m = string b (string_of_mode m);;

(***********************************************************************)
(** addressing modes *)
(***********************************************************************)

let string_of_add_mode = function
  | Data -> "Mode1"
  | LoadWord -> "Mode2"
  | LoadMisc -> "Mode3"
  | LoadMul -> "Mode4"
  | LoadCoproc -> "Mode5";;

let add_mode b m = string b (string_of_add_mode m);;

(***********************************************************************)
(** functions and binary operators *)
(***********************************************************************)

let string_of_fun_name = function
  | "NOT" -> "not"
  | "not" -> "negb"
  | s -> s;;

let add_state = function
  | "next_inst_address" | "cur_inst_address" | "CurrentModeHasSPSR"
  | "InAPrivilegedMode" | "ConditionPassed" | "CP15_reg1_EEbit"
  | "CP15_reg1_Ubit" as s -> s ^ " s0"
  | s -> s;;

let fun_name b s = string b (add_state (string_of_fun_name s));;

let string_of_binop = function
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

let binop b s = string b (string_of_binop s);;

(***********************************************************************)
(** expressions *)
(***********************************************************************)

(*REMOVE when finished! *)
let todo_exp s b e = bprintf b "(*todo: %a*) %s" Genpc.exp e s;;
let todo_word = todo_exp "(repr 0)";;
let todo_bool = todo_exp "true";;

let is_not_num = function
  | Num _ -> false
  | _ -> true;;

let rec pexp b = function
  | Var _ as e -> exp b e
  | e -> par exp b e

and num_exp b = function
  | Num s -> num b s
  | e -> pexp b e

and regnum_exp b = function
  | Num s -> regnum b s
  | Var s -> string b s
  | e -> bprintf b "(mk_regnum %a)" pexp e

and address b e = bprintf b "(mk_address %a)" pexp e

and nat_exp b e = bprintf b "(nat_of_Z %a)" pexp e

and exp b = function
  | Bin s -> word bin b s
  | Hex s -> word hex b s
  | Num s -> word num b s
  | Var s -> string b s

  | Fun (("Shared"|"IsExclusiveGlobal"|"IsExclusiveLocal"), _) as e ->
      (*FIXME*) todo_bool b e
  | Fun (("CPSR_with_specified_E_bit_modification"|"TLB"|"ExecutingProcessor"
	 |"accvalue"), _) as e -> (*FIXME*) todo_word b e

  | Fun (f, []) -> fun_name b f
  | Fun ("SignedSat"|"SignedDoesSat"|"UnsignedSat"|"UnsignedDoesSat" as f,
	 [e1; e2]) when is_not_num e2 -> (* add a cast *)
      bprintf b "%a %a %a" fun_name f pexp e1 nat_exp e2
  | Fun (f, es) -> bprintf b "%a %a" fun_name f (list " " num_exp) es

  | BinOp (e1, ("==" as f), Num n) -> (* optimization avoiding a repr *)
      bprintf b "%a %a %a" binop f pexp e1 num n
  | BinOp (e1, f, e2) -> bprintf b "%a %a %a" binop f pexp e1 pexp e2

  | If_exp (e1, e2, e3) ->
      bprintf b "if %a then %a else %a" exp e1 exp e2 exp e3
  | CPSR -> string b "cpsr s0"
  | Range (e, r) -> bprintf b "%a[%a]" pexp e range r
  | Memory (e, n) -> bprintf b "read s0 %a %a" address e size n

  | SPSR None -> string b "spsr s0 None"
  | SPSR (Some m) -> bprintf b "spsr s0 (Some %a)" exn_mode m

  | Reg (e, None) -> bprintf b "reg_content s0 %a" regnum_exp e
  | Reg (e, Some m) ->
      bprintf b "reg_content_mode s0 %a %a" regnum_exp e mode m

  | Coproc_exp (_, _, _) as e -> todo_word b e

  | Other _ | Unpredictable_exp | Unaffected -> invalid_arg "Gencoq.exp"

and range b = function
  | Flag (s, _) -> bprintf b "%sbit" s
  | Index e -> num_exp b e
  | Bits (n1, n2) -> bprintf b "%a#%a" num n1 num n2;;

(***********************************************************************)
(** instructions *)
(***********************************************************************)

(*REMOVE when finished! *)
let todo f b e = bprintf b "todo \"%a\"" f e;;

let rec inst k b i = indent b k; inst_aux k b i

and pinst k b i = indent b k; par (inst_aux k) b i

and inst_cons k b = function
  | Affect (Var _, _) as i -> inst k b i
  | i -> indent b k; postfix " ::" (inst_aux k) b i

and inst_aux k b = function
  | Unpredictable -> string b "unpredictable \"\""
      (*FIXME: replace empty string by program name*)
  | Block is ->
      bprintf b "block (\n%a\n%anil)"
	(list "\n" (inst_cons (k+2))) is indent (k+2)
  | If (e, i, None) -> bprintf b "if_then %a\n%a" pexp e (pinst (k+2)) i
  | If (e, i1, Some i2) ->
      bprintf b "if_then_else %a\n%a\n%a"
	pexp e (pinst (k+2)) i1 (pinst (k+2)) i2
  | Affect (e, v) as i ->
      begin try affect b v e
      with Not_found -> todo (Genpc.inst 0) b i end
  | Proc _ | While _ | For _ | Coproc _ | Case _ as i ->
      todo (Genpc.inst 0) b i
  | Misc _ | Assert _ -> invalid_arg "Gencoq.inst"

and affect b v = function
  | Var s -> bprintf b "let %s := %a in" s exp v
  | Range (e, r) -> bprintf b "%a (%a %a %a)" set e range r pexp v pexp e
  | e -> bprintf b "%a %a" set e pexp v

and range b = function
  | Flag (s, _) -> bprintf b "set_bit %sbit" s
  | Index i -> bprintf b "set_bit %a" num_exp i
  | Bits (p, q) -> bprintf b "set_bits %a %a" num p num q

and set b = function
  | Reg (e, None) -> bprintf b "set_reg %a" regnum_exp e
  | Reg (e, Some m) -> bprintf b "set_reg_mode %a %a" mode m regnum_exp e
  | CPSR -> bprintf b "set_cpsr"
  | SPSR None -> bprintf b "set_spsr None"
  | SPSR (Some m) -> bprintf b "set_spsr (Some %a)" exn_mode m
  | Memory (e, n) -> bprintf b "write %a %a" address e size n
  | _ -> raise Not_found;;

(***********************************************************************)
(** semantic step function of some instruction *)
(***********************************************************************)

let ident b i =
  bprintf b "%s%a%a" i.iname (list "" string) i.iparams
    (option "" string) i.iversion;;

let add_mode b n = add_mode b (add_mode_of_name n);;

let operand b n =
  bprintf b "%a_%a" add_mode n string (Preproc.underscore (snd n));;

let arg b (v, t) = bprintf b "(%s : %s)" v t;;

let prog gs b p =
  bprintf b "(* %s %a *)\nDefinition " p.pref Genpc.prog_name p;
  (match p.pname with
    | Inst (id, _) ->
	bprintf b "%a_step (s0 : state) %a : result :=\n%a true s0.\n"
	  ident id
    | Oper n ->	bprintf b "%a_step %a :=\n%a.\n" operand n)
    (list " " arg) gs (inst 2) p.pinst;;

(***********************************************************************)
(** constructor of some instruction *)
(***********************************************************************)

let inst_typ gs b = function
  | Oper _ -> () (*FIXME*)
  | Inst (id, _) -> bprintf b "| %a %a" ident id (list " " arg) gs;;

(***********************************************************************)
(** call to the semantics step function of some instruction *)
(***********************************************************************)

let var_name b (v, _) = bprintf b "%s" v;;

let inst_sem gs b = function
  | Oper _ -> () (*FIXME*)
  | Inst (id, _) ->
      bprintf b "    | %a %a =>" ident id (list " " var_name) gs;
      if List.exists ((=) ("shifter_operand", "word")) gs then
	if List.exists ((=) ("shifter_carry_out", "bool")) gs then 
	  bprintf b "\n      let (v, shifter_carry_out) := shifter_operand_value_and_carry s0 w shifter_operand in\n       "
	else
	bprintf b "\n      let (v, _) := shifter_operand_value_and_carry s0 w shifter_operand in\n       ";
      bprintf b " %a_step %a v s0" ident id (list " " var_name) gs;;

(***********************************************************************)
(** Main coq generation function.
For each instruction:
- generate its semantics step function
- generate the corresponding constructor for the type of instructions
- generate the call to its semantics step function in the general
semantics step function *)
(***********************************************************************)

(*FIXME/REMOVE?*)
let lsm_hack p =
  match p.pname with
    | Inst ({ iname = "LDM" | "STM" }, _) ->
	(* add 'if (W) then Rn = new_Rn' at the end of the main 'if' *)
	let a = If (Var "W", Affect (Reg (Var "n", None), Var "n"), None) in
	let i = match p.pinst with
          | If (c, Block ids, None) -> If (c, Block (ids @ [a]), None)
          | Block [x; If (c, Block ids, None)] ->
              Block [x; If (c, Block (ids @ [a]), None)]
          | _ -> invalid_arg "Gencoq.lsm_hack"
	in { p with pinst = i }
    | Oper n when add_mode_of_name n = LoadMul ->
	(* replace 'If (...) then Rn = ...' by 'new_Rn = ...' *)
	let rec inst = function
	  | Block ids -> Block (List.map inst ids)
	  | If (_, Affect (Reg (Var "n", None), e), None) ->
	      Affect (Var "new_Rn", e)
	  | i -> i
	in { p with pinst = inst p.pinst }
    | Oper _ | Inst _ -> p;;

let lib b ps =
  let btyp = Buffer.create 10000 in
  let bsem = Buffer.create 10000 in
  let prog_typ_sem p =
    let p = lsm_hack p in (*FIXME*)
    let gs, _ = variables p in
      bprintf b "%a\n" (prog gs) p;
      bprintf btyp "%a\n" (inst_typ gs) p.pname;
      bprintf bsem "%a\n" (inst_sem gs) p.pname
  in
    bprintf b "Require Import Bitvec List Integers Util Functions Config Arm State Semantics.\nRequire Import ZArith.\nImport Int.\n\nModule Inst (Import C : CONFIG).\n\n";
    List.iter prog_typ_sem ps;
    bprintf b "Inductive instruction : Type :=\n";
    Buffer.add_buffer b btyp;
    bprintf b "\nDefinition execute (w : word) (i : instruction) (s0 : state) : result :=\n  match i with\n";
    Buffer.add_buffer b bsem;;
