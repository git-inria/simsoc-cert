(**
SimSoC-Cert, a library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Transform an AST into an AST ready for code generation.
*)

open Ast;;
open Printf;;
open Util;;

(***********************************************************************)
(** normalization of expressions *)
(***********************************************************************)

let string_of_op = function
  | "+" -> "add"
  | "-" -> "sub"
  | s -> s;;

let underscore =
  let b = Buffer.create 100 in
    fun ss ->
      Buffer.clear b;
      list "_" string b ss;
      Buffer.contents b;;

let rec exp = function

  (* we only consider ARMv5 and above *)
  | If_exp (Var "v5_and_above", e, _) -> exp e

  (* replace the incorrect function call to R by a register value *)
  | Fun ("R", e :: _) -> Reg (e, None)

  (* replace opcode[n] by a variable *)
  | Range (Var ("opcode" as s), Index (Num n)) -> Var (s ^ n)

  (* replace some "variables" by function calls *)
  | Var ("UnallocMask"|"StateMask"|"UserMask"|"PrivMask"
    |"CP15_reg1_EEbit"|"CP15_reg1_Ubit"|"accvalue" as s) -> Fun (s, [])

  (* replace "mode" by "CPSR[4:0]", and "GE" by "CPSR[19:16]" *)
  | Var "mode" -> Range (CPSR, Bits ("4", "0"))
  | Var "GE" -> Range (CPSR, Bits ("19", "16"))

  (* normalize ranges *)
  | Range (e1, Index e2) -> range (exp e1) (Index (exp e2))
  | Range (e, r) -> range (exp e) r
 
  (* replace English expressions by function calls *)
  | Other ss ->
      begin match underscore ss with
	| "address_of_BKPT_instruction" -> Fun ("cur_inst_address", [])
	| "address_of_the_instruction_after_the_branch_instruction"
	| "address_of_instruction_after_the_BLX_instruction"
	| "address_of_the_instruction_after_the_BLX_instruction"
	| "address_of_next_instruction_after_the_SWI_instruction"
	  -> Fun ("next_inst_address", [])
	| f -> Fun (f, [])
      end

  (* rename some function calls depending on the argument,
     and change the argument into a list of arguments,
     e.g. CarrayFrom(a+b) is replaced by CarryFrom_add2(a,b) *)
  | Fun (("OverflowFrom"|"BorrowFrom"|"CarryFrom"|"CarryFrom8"|"CarryFrom16"
	      as f), (BinOp (_, op, _) as e) :: _) -> let es = args e in
      Fun (sprintf "%s_%s%d" f (string_of_op op) (List.length es),
	   List.map exp es)

  (* normalize if-expressions wrt Unpredictable_exp's *)
  | If_exp (_, e1, e2) when e1 = e2 -> exp e1
  | If_exp (c0, If_exp (c1, Unpredictable_exp, e1), e2) ->
      exp (If_exp (BinOp (c0, "and", c1),
		   Unpredictable_exp,
		   If_exp (Fun ("not", [c0]), e2, e1)))
  | If_exp (c0, If_exp (c1, e1, Unpredictable_exp), e2) ->
      exp (If_exp (BinOp (c0, "and", Fun ("not", [c1])),
		   Unpredictable_exp,
		   If_exp (Fun ("not", [c0]), e2, e1)))
  | If_exp (c0, e0, If_exp (c1, Unpredictable_exp, e1)) ->
      exp (If_exp (BinOp (Fun ("not", [c0]), "and", c1),
		   Unpredictable_exp,
		   If_exp (c0, e0, e1)))
  | If_exp (c0, e0, If_exp (c1, e1, Unpredictable_exp)) ->
      exp (If_exp (BinOp (Fun ("not", [c0]), "and", Fun ("not", [c1])),
		   Unpredictable_exp,
		   If_exp (c0, e0, e1)))

  (* recursive expressions *)
  | Fun (f, es) -> Fun (f, List.map exp es)
  | BinOp (e1, f, e2) -> BinOp (exp e1, f, exp e2)
  | If_exp (e1, e2 ,e3) -> If_exp (exp e1, exp e2, exp e3)
  | Memory (e, n) -> Memory (exp e, n)
  | Coproc_exp (e, s, es) -> Coproc_exp (exp e, s, List.map exp es)
  | Reg (e, m) -> Reg (exp e, m)

  (* non-recursive expressions *)
  | Num _|Bin _|Hex _|CPSR|SPSR _|Var _|Unaffected|Unpredictable_exp as e
    -> e

(* replace two successive ranges by a single range *)
and range =
  let tni s = Scanf.sscanf s "%i" (fun x -> x)
  and int k = sprintf "%i" k in
    fun e r ->
      match e with
	| Range (e1, Bits (_, n)) ->
	    begin match r with
	      | Bits (p1, p2) ->
		  let n = tni n and p1 = tni p1 and p2 = tni p2 in
		    Range (e1, Bits (int (n+p1), int (n+p2)))
	      | Index (Num p) ->
		  let n = tni n and p = tni p in
		    Range (e1, Index (Num (int (n+p))))
	      | r -> Range (e, r)
	    end
	| e -> Range (e, r);;

(***********************************************************************)
(** normalization of blocks *)
(***********************************************************************)

let rec raw_inst = function
  | Block is ->
      begin match raw_block is with
	| [i] -> i
	| is -> Block is
      end
  | i -> i

and raw_block = function
  | [] -> []
  | i :: is ->
      begin match raw_inst i with
	| Block is' -> is' @ raw_block is
	| i -> i :: raw_block is
      end;;

(***********************************************************************)
(** normalization of instructions *)
(***********************************************************************)

let nop = Block [];;

let is_nop = (=) nop;;

let lc_decl = ["value"; "operand" ; "operand1" ; "operand2"; "data";
	       "diff1"; "diff2"; "diff3"; "diff4"; "mask"];;

let rec inst = function

  (* we only consider ARMv5 and above *)
  | If (Var "v5_and_above", i, _) -> inst i

  (* normalize block's *)
  | Block is -> raw_inst (Block (List.map inst is))

  (* replace assert's and memory access indications by nop's *)
  | Proc ("MemoryAccess", _) | Assert _ -> nop

  (* replace English expressions by procedure calls *)
  | Misc ss -> Proc (underscore ss, [])

  (* replace affectations to Unaffected by nop's *)
  | Affect (e1, e2) ->
      begin match exp e2 with
	| Unaffected -> nop
	| e2 -> Affect (exp e1, e2)
      end

  (* simplify conditional instructions wrt nop's *)
  | If (c, i, None) ->
      let i = inst i in
	if is_nop i then nop else If (exp c, i, None)
  | If (c, i1, Some i2) ->
      let i1 = inst i1 and i2 = inst i2 in
	if is_nop i2 then
	  if is_nop i1
	  then nop
	  else If (exp c, i1, None)
	else
	  if is_nop i1
	  then If (Fun ("NOT", [exp c]), i2, None)
	  else
	    (* local declaration in if branches *)
	    begin match i1, i2 with
	      | Affect (Var v1 as x, e1), Affect (Var v2, e2)
		  when v1 = v2 && List.mem v1 lc_decl ->
		  inst (Affect (x, If_exp (c, e1, e2)))
	      | Affect (Var v as x, e), Unpredictable
		  when List.mem v lc_decl ->
		  inst (Affect (x, If_exp (c, e, Unpredictable_exp)))
	      | Unpredictable, Affect (Var v as x, e)
		  when List.mem v lc_decl -> 
		  inst (Affect (x, If_exp (c, Unpredictable_exp, e)))
	      | _ -> If (exp c, i1, Some i2)
	    end

  (* recursive instructions *)
  | Proc (f, es) -> Proc (f, List.map exp es)
  | While (e, i) -> While (exp e, inst i)
  | For (s, n, p, i) -> For (s, n, p, inst i)
  | Coproc (e, s, es) -> Coproc (exp e, s, List.map exp es)
  | Case (e, s) -> Case (exp e, List.map (fun (n, i) -> (n, inst i)) s)

  (* non-recursive instructions *)
  | Unpredictable -> Unpredictable;;

(***********************************************************************)
(** normalization of affectations
- replace affectation of Unpredictable_exp by Unpredictable
- replace conditional affectation of Unpredictable by an equivalent block *)
(***********************************************************************)

let rec affect = function

  | Block is -> Block (affects is)

  | Affect (_, Unpredictable_exp) -> Unpredictable
  | Affect (e1, If_exp (c, Unpredictable_exp, e2)) ->
      Block [If (c, Unpredictable, None); Affect (e1, e2)]

  | If (e, i, None) -> If (e, affect i, None)
  | If (e, i1, Some i2) -> If (e, affect i1, Some (affect i2))
  | While (e, i) -> While (e, affect i)
  | For (s, n, p, i) -> For (s, n, p, affect i)
  | Case (e, s) -> Case (e, List.map (fun (n, i) -> (n, affect i)) s)

  | i -> i

and affects = function
  | [] -> []
  | i :: is ->
      begin match affect i with
	| Block is' -> is' @ affects is
	| i -> i :: affects is
      end;;

(***********************************************************************)
(** normalization of programs *)
(***********************************************************************)

let prog p = { p with pinst = affect (inst p.pinst) };;

(***********************************************************************)
(** global and local variables of a program *)
(***********************************************************************)

module type Var = sig
  type typ;;
  val global_type : string -> typ;;
  val local_type : string -> exp -> typ;;
  val key_type : typ;;
end;;

module Make (G : Var) = struct

  let rec vars_exp ((gs,ls) as acc) = function
    | Var s when not (StrMap.mem s ls || s = "i") ->
	(* "i" is used in loops *)
	StrMap.add s (G.global_type s) gs, ls
    | If_exp (e1, e2, e3) -> vars_exp (vars_exp (vars_exp acc e1) e2) e3
    | Fun (_, es) -> vars_exps acc es
    | Range (e1, Index e2) | BinOp (e1, _, e2) -> vars_exp (vars_exp acc e1) e2
    | Range (e, _) | Reg (e, _) | Memory (e, _) -> vars_exp acc e
    | Coproc_exp (e, _ , es) -> vars_exps (vars_exp acc e) es
    | _ -> acc

  and vars_exps acc es = List.fold_left vars_exp acc es;;

  let output_registers = set_of_list ["d"; "dHi"; "dLo"; "n"];;

  let rec vars_inst ((gs,ls) as acc) = function
    | Affect (Var s, e) | Affect (Range (Var s, _), e) -> vars_exp
	(if StrMap.mem s gs || StrMap.mem s ls || s = "i"
	 then acc
	 else
	   if StrSet.mem s output_registers
	   then StrMap.add s (G.global_type s) gs, ls
	   else gs, StrMap.add s (G.local_type s e) ls) e
    | Affect (e1, e2) -> vars_exp (vars_exp acc e1) e2
    | Block is -> vars_insts acc is
    | If (e, i, None) | While (e, i) -> vars_inst (vars_exp acc e) i
    | If (e, i1, Some i2) -> vars_inst (vars_inst (vars_exp acc e) i1) i2
    | Proc (_, es) -> vars_exps acc es
    | For (_, _, _, i) -> vars_inst acc i
    | Coproc(e, _ , es) -> vars_exps (vars_exp acc e) es
    | Case (Var s, nis) -> vars_cases
	(if StrMap.mem s ls || s = "i" then acc
	 else StrMap.add s G.key_type gs, ls) nis
    | _ -> acc

  and vars_insts acc is = List.fold_left vars_inst acc is

  and vars_cases acc nis =
    List.fold_left (fun acc (_, i) -> vars_inst acc i) acc nis;;

  let vars p = vars_inst (StrMap.empty, StrMap.empty) p.pinst;;

end;;
