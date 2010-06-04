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

(*****************************************************************************)
(** variable types *)
(*****************************************************************************)

module G = struct

  type typ = string;;

  (* heuristic giving a type to a variable from its name *)
  let type_of_var = function
    | "cond" -> "opcode"
    | "mmod" | "opcode25" | "shift" -> "bool"
    | "n" | "d" | "m" | "s" | "dHi" | "dLo" -> "regnum"
    | s -> if String.length s = 1 then "bool" else "word";;

  (* the type of global variables is given by their names *)
  let global_type = type_of_var;;

  (* type for memory values *)
  let type_of_size = function
    | Byte -> "byte"
    | Half -> "half"
    | Word -> "word";;

  (* the type of a local variable is given by its name, except when it
     is affected to some memory value *)
  let local_type s e =
    match e with
      | Memory (_, n) -> type_of_size n
      | _ -> type_of_var s;;

  (* type of variables used in case instructions *)
  let case_type = "word";;

end;;

module V = Ast.Make(G);;

(*****************************************************************************)
(** numbers *)
(*****************************************************************************)

(* convert a number string into a Coq integer *)
let num = string;;

(* convert a string of the form 0b[01]* into a Coq integer *)
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

(* convert a string of the form 0x[0-9a-f]* into a Coq integer *)
(*IMPROVE: use a Coq function to convert an hexa string into a word*)
let hex b s =
  let n = Scanf.sscanf s "%li" (fun x -> x) in
    if Int32.compare n Int32.zero = 0 then bprintf b "Z0"
    else bprintf b "Zpos %lu" n;;

let hex b s = par hex b s;;

(* convert a number string into a Coq word by first converting the
   string into a Coq integer using f and then applying the Coq repr
   function *)
let word f b s = bprintf b "repr %a" f s;;

(*****************************************************************************)
(** registers *)
(*****************************************************************************)

(* convert a number string into a register number using the Coq
   mk_regnum function (use some pre-defined constant for some special
   registers) *)
let string_of_regnum = function
  | "15" -> "PC"
  | "14" -> "LR"
  | "13" -> "SP"
  | s -> Printf.sprintf "(mk_regnum %s)" s;;

let regnum b s = string b (string_of_regnum s);;

(*****************************************************************************)
(** memory size *)
(*****************************************************************************)

let string_of_size = function
  | Byte -> "Byte"
  | Half -> "Half"
  | Word -> "Word";;

let size b s = string b (string_of_size s);;

(*****************************************************************************)
(** processor and addressing modes *)
(*****************************************************************************)

let exn_mode = Genpc.mode;;

let string_of_mode = function
  | Usr -> "usr"
  | Sys -> "sys"
  | m -> "(exn " ^ Genpc.string_of_mode m ^ ")";;

let mode b m = string b (string_of_mode m);;

let addr_mode b m = bprintf b "M%d" m;;

(*****************************************************************************)
(** functions and binary operators *)
(*****************************************************************************)

let depend_on_state = function
  | "address_of_next_instruction" | "address_of_current_instruction"
  | "CurrentModeHasSPSR" | "InAPrivilegedMode" | "ConditionPassed"
  | "ExecutingProcessor" | "IsExclusiveGlobal" | "IsExclusiveLocal"
  | "TLB" | "Shared" | "high_vectors_configured" -> true
  | _ -> false;;

let depend_on_config = function
  | "JE_bit_of_Main_Configuration_register" | "SUB_ARCHITECTURE_DEFINED_value"
  | "CV_bit_of_Jazelle_OS_Control_register"
  | "Jazelle_Extension_accepts_opcode_at" -> true
  | _ -> false;;

let string_of_fun_name = function
  | "NOT" -> "not"
  | "not" -> "negb"
  | s when depend_on_config s -> "C." ^ s
  | s when depend_on_state s -> s ^ " s0"
  | s -> s;;

let fun_name b s = string b (string_of_fun_name s);;

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

let is_cp15_reg1 s =
  String.length s > 10 && String.sub s 0 10 = "CP15_reg1_";;

(*****************************************************************************)
(** expressions *)
(*****************************************************************************)

(*FIXME: raise an exception instead of use a todo for the instruction
  containing this expression*)

(*REMOVE when finished*)
let todo_exp s b e = bprintf b "(*todo: %a*) %s" Genpc.exp e s;;
let todo_word = todo_exp "(repr 0)";;

let is_not_num = function
  | Num _ -> false
  | _ -> true;;

(* add parentheses around complex expressions *)
let rec pexp b = function
  | Var _ as e -> exp b e
  | Fun (f, []) as e when depend_on_config f -> exp b e
  | e -> par exp b e

(* like pexp but prints numbers as integers (not words) *)
and num_exp b = function
  | Num s -> num b s
  | e -> pexp b e

(* convert an expression into a register number using the Coq function
   mk_regnum except if it is a number or a variable *)
and regnum_exp b = function
  | Num s -> regnum b s
  | Var s -> string b s
  | e -> bprintf b "(mk_regnum %a)" pexp e

(* convert an expression into an address using the Coq function
   mk_address *)
and address b e = bprintf b "(mk_address %a)" pexp e

(* convert an expression into a Coq natural number using the Coq
   function nat_of_Z *)
and nat_exp b e = bprintf b "(nat_of_Z %a)" pexp e

and exp b = function
    (* convert numbers into Coq words *)
  | Bin s -> word bin b s
  | Hex s -> word hex b s
  | Num s -> word num b s
  | Var s -> string b s

  (*FIXME: functions not supported yet*)
  | Coproc_exp _ as e -> todo_word b e

  (* optimization: since, in SimSoC-Cert, everything is represented by
     words, zero-extension is always done (implicitly) and does not
     need to be applied explicitly *)
  | Fun ("ZeroExtend", e :: _) -> bprintf b "(*ZeroExtend*)%a" exp e

  (* system coprocessor register bits *)
  | Fun (f, _) when is_cp15_reg1 f ->
      bprintf b "(CP15_reg1 s0)[%s]" (String.sub f 10 (String.length f - 10))

  (* print no parenthesis if there is no argument (functions are
     curryfied in Coq) *)
  | Fun (f, []) -> fun_name b f
  (* for saturation functions, add a cast to nat if the second
     argument is not a number *)
  | Fun ("SignedSat"|"SignedDoesSat"|"UnsignedSat"|"UnsignedDoesSat" as f,
	 [e1; e2]) when is_not_num e2 -> (* add a cast *)
      bprintf b "%a %a %a" fun_name f pexp e1 nat_exp e2
  (* default printing of function calls *)
  | Fun (f, es) -> bprintf b "%a %a" fun_name f (list " " num_exp) es

  (* optimization avoiding a call to repr *)
  | BinOp (e1, ("==" as f), Num n) ->
      bprintf b "%a %a %a" binop f pexp e1 num n
  (* default printing of binary operators (like function calls) *)
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

  | Unpredictable_exp | Unaffected -> invalid_arg "Gencoq.exp"

and range b = function
  (* convert the flag named s into the pre-defined Coq constant sbit *)
  | Flag (s, _) -> bprintf b "%sbit" s
  (* add a cast to nat when the index is a complex expression *)
  | Index (BinOp (_, "-", _) as e) -> nat_exp b e
  | Index e -> num_exp b e
  (* convert a bit range into a Coq bit range *)
  | Bits (n1, n2) -> bprintf b "%a#%a" num n1 num n2;;

(*****************************************************************************)
(** instructions *)
(*****************************************************************************)

(*REMOVE when finished! *)
let todo f b x = bprintf b "todo \"%a\"" f x;;

let case k b (n, i) =
  match i with
    | Affect (_, e) -> indent b k; bprintf b "| %a => %a\n" bin n exp e
    | _ -> raise Not_found;;

let rec inst k b i = indent b k; inst_aux k b i

and pinst k b i = indent b k; par (inst_aux k) b i

and inst_cons k b = function
  | Affect (Var _, _) as i -> inst k b i
  | i -> indent b k; postfix " ::" (inst_aux k) b i

and inst_aux k b = function
  (*FIXME: to be done*)
  | Proc ("Start_opcode_execution_at", _) | While _ | Coproc _ as i ->
      todo (Genpc.inst 0) b i

  | Assert _ -> invalid_arg "Gencoq.inst_aux"

  | Unpredictable -> string b "unpredictable \"\""
      (*FIXME: replace empty string by program name*)

  | Block [] -> string b "block nil"
  | Block is ->
      bprintf b "block (\n%a\n%anil)"
	(list "\n" (inst_cons (k+2))) is indent (k+2)

  | If (e, i1, None) ->
      bprintf b "if_then %a\n%a" pexp e (pinst (k+2)) i1
  | If (e, i1, Some i2) ->
      bprintf b "if_then_else %a\n%a\n%a"
	pexp e (pinst (k+2)) i1 (pinst (k+2)) i2

  (* try to generate the code of an affectation; in case of failure,
     output a "todo" *)
  | Affect (e, v) as i ->
      begin try affect b v e
      with Not_found -> todo (Genpc.inst 0) b i end

  (* adhoc treatment of case's: as case's are only used for defining
     the variable index, we convert a case which branches define index
     into a let index := followed by a Coq match *)
  | Case (e, nis) as i ->
      begin try bprintf b
	"let index :=\n%amatch unsigned %a with\n%a%a| _ => repr 0\n%aend in"
	indent (k+2) exp e (list "" (case (k+4))) nis indent (k+4) indent (k+2)
      with Not_found -> todo (Genpc.inst 0) b i end

  | For (x, p, q, i) ->
      bprintf b "loop %s %s (fun %s =>\n%a)" p q x (inst (k+2)) i

  (* print no parenthesis if there is no argument (functions are
     curryfied in Coq) *)
  | Proc (f, []) -> fun_name b f
  (* default printing of function calls *)
  | Proc (f, es) -> bprintf b "%a %a" fun_name f (list " " num_exp) es

and affect b v = function
  (* an affectation of a variable is converted into a Coq "let" *)
  | Var s -> bprintf b "let %s := %a in" s exp v
  (* otherwise, we use some Coq update function *)
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

(*****************************************************************************)
(** semantic function of a program *)
(*****************************************************************************)

(* program name *)

let ident b i =
  bprintf b "%s%a%a" i.iname (list "" string) i.iparams
    (option "" string) i.ivariant;;

let name b p =
  match p.pkind with
    | Inst -> ident b p.pident
    | Mode m -> bprintf b "%a_%a" addr_mode m ident p.pident;;

(* result type of a program *)

let mode_var_typ b = function
(*REMOVE?  | "shifter_carry_out" -> string b " * bool"*)
  | _ -> string b " * word";;

let result b p =
  match p.pkind with
    | Inst -> ()
    | Mode k -> list "" mode_var_typ b (mode_vars k);;

(* split an instruction block into two blocks:
- the prefix of the block consisting of the affectations and cases
- the remainder of the instructions *)

let is_affect = function Affect _ | Case _ -> true | _ -> false;;

let split = function
  | Block is -> firsts is_affect is
  | Affect _ as i -> [i], []
  | i -> [], [i];;

let block k b i =
  let is1, is2 = split i in
    List.iter (endline (inst k) b) is1;
    bprintf b "%alet r := %a true s0 in" indent k (inst_aux k) (Block is2);;

(* default result component value *)
let default b _ = string b ", repr 0";;

let mode_var b = function
(*REMOVE?  | "shifter_carry_out" as s -> bprintf b ", zne 0 %s" s*)
  | s -> bprintf b ", %s" s;;

(* FIXME: programs which normalized form do not consist of affectations only
  are not handled yet. Moreover, they use while-loops... *)
let problems = set_of_list ["A5.5.2";"A5.5.3";"A5.5.4";"A5.5.5"];;

let pinst b p =
  match p.pkind with
    | Inst -> bprintf b "%a true s0" (inst 2) p.pinst
    | Mode k ->
	let ls = mode_vars k in
	  if StrSet.mem p.pref problems then
	    bprintf b "  let r := %a true s0 in\n    (r%a)"
	      (todo (Genpc.inst 0)) p.pinst (list "" default) ls
	else
	  match p.pinst with
	    | If (e, i, None) ->
		bprintf b "  if %a then\n%a\n    (r%a)\n  else (Ok false s0%a)"
		  exp e (block 4) i
		  (list "" mode_var) ls (list "" default) ls
	    | i ->
		bprintf b "%a\n    (r%a)" (block 2) i
		  (list "" mode_var) ls;;

let arg_typ b (x, t) = bprintf b " (%s : %s)" x t;;

let semfun b p gs =
  bprintf b
    "(* %s %a *)\nDefinition %a_step (s0 : state)%a : result%a :=\n%a.\n\n"
    p.pref Genpc.name p name p (list "" arg_typ) gs result p pinst p;;

(*****************************************************************************)
(** constructor declaration corresponding to a program *)
(*****************************************************************************)

let constr bcons_inst bcons_mode p gs =
  match p.pkind with
    | Inst -> let b = bcons_inst in
	begin match addr_mode_of_prog p gs with
	  | Some k ->
	      bprintf b "\n| %a (m_ : mode%d)%a"
		name p k (list "" arg_typ) (remove_mode_vars gs)
		(* mode variables are not constructor arguments since
		   they are computed from the mode argument *)
	  | None -> bprintf b "\n| %a%a" name p (list "" arg_typ) gs
	end
    | Mode k -> let b = bcons_mode.(k-1) in
	bprintf b "\n| %a%a" name p (list "" arg_typ) gs;;

(*****************************************************************************)
(** call to the semantics function of some instruction *)
(*****************************************************************************)

(* we rename some argument names to avoid name clashes or warnings in Coq *)
let string_of_arg =
  let set = set_of_list
    ["S";"R";"I";"mode";"StateMask";"PrivMask";"shift"] in
    fun s -> if StrSet.mem s set then s ^ "_" else s;;

let arg b (x, _) = bprintf b " %s" (string_of_arg x);;

let args = list "" arg;;

let call bcall_inst bcall_mode p gs =
  match p.pkind with
    | Inst -> let b = bcall_inst in
	begin match addr_mode_of_prog p gs with
	  | None ->
	      bprintf b "    | %a%a =>" name p args gs;
	      bprintf b " %a_step s0%a\n" name p args gs
	  | Some k ->
	      bprintf b "    | %a m_%a =>" name p args (remove_mode_vars gs);
	      bprintf b
		"\n      match mode%d_step s0 m_ with (r%a) =>\n        "
		k (list "" mode_var) (mode_vars k);
	      bprintf b " %a_step s0%a end\n" name p args gs
	end
    | Mode k -> let b = bcall_mode.(k-1) in
	bprintf b "    | %a%a =>" name p args gs;
	bprintf b " %a_step s0%a\n" name p args gs;;

(*****************************************************************************)
(** Main coq generation function.
For each instruction:
- generate its semantic function
- generate the corresponding constructor for the type of instructions
- generate the call to its semantics function *)
(*****************************************************************************)

let lib b ps =
  let bcons_inst = Buffer.create 5000
  and bcons_mode = Array.init 5 (fun _ -> Buffer.create 1000)
  and bcall_inst = Buffer.create 5000
  and bcall_mode = Array.init 5 (fun _ -> Buffer.create 1000)
  and bsem = Buffer.create 100000 in
  let prog p =
    let gs, _ = V.vars p in
      semfun bsem p gs;
      constr bcons_inst bcons_mode p gs;
      call bcall_inst bcall_mode p gs
  in
    (* generate code *)
    List.iter prog ps;
    (* print preamble *)
    bprintf b
"(* File generated by SimSoC-Cert. It provides the definitions of the types
of ARMv6 addressing modes and instructions, and their semantics. *)\n\nRequire Import Bitvec List Util Functions Config Arm SCC State Semantics ZArith.\n\n";
    (* print type definitions *)
    for k = 1 to 5 do
      bprintf b "(* Addressing mode %d *)\nInductive mode%d : Type :=%a.\n\n"
	k k Buffer.add_buffer bcons_mode.(k-1)
    done;
    bprintf b "(* Instructions *)\nInductive inst : Type :=%a.\n\n" Buffer.add_buffer bcons_inst;
    (* print semantic functions *)
    bprintf b "(* Semantic functions of addressing modes and instructions *)\nModule InstSem (Import C : CONFIG).\n\n";
    Buffer.add_buffer b bsem;
    for k = 1 to 5 do
      bprintf b "(* Semantic function for addressing mode %d *)\nDefinition mode%d_step (s0 : state) (m : mode%d) :=\n  match m with\n%aend.\n\n" k k k Buffer.add_buffer bcall_mode.(k-1)
    done;
    bprintf b "(* Semantic function for instructions *)\nDefinition step (s0 : state) (i : inst) : result :=\n  match i with\n%aend.\n\n" Buffer.add_buffer bcall_inst;
    bprintf b "End InstSem.\n";;
