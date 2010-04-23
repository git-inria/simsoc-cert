(**
SimSoC-Cert, a library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Transform a raw AST into an AST ready for code generation.
*)

open Ast;;
open Printf;;
open Util;;

(***********************************************************************)
(** program variables *)
(***********************************************************************)

module type Var = sig
  type typ;;
  val global_type : string -> typ;;
  val local_type : string -> exp -> typ;;
  val key_type : typ;;
end;;

module Make (G : Var) = struct

  let input_registers = set_of_list ["n"; "m"; "s"];;
  let output_registers = set_of_list ["d"; "dHi"; "dLo"; "n"];;

(*REMOVE: if transformed into function calls*) 
  let specials = set_of_list
    ["CP15_reg1_EEbit"; "CP15_reg1_Ubit"; "GE"; "i"; "v5_and_above";
     "UnallocMask"; "StateMask"; "UserMask"; "PrivMask"];;

  let rec vars_exp ((gs,ls) as acc) = function
    | Var s ->
	if StrMap.mem s gs || StrMap.mem s ls || StrSet.mem s specials
	then acc
	else StrMap.add s (G.global_type s) gs, ls
    | If_exp (e1, e2, e3) -> vars_exp (vars_exp (vars_exp acc e1) e2) e3
    | Fun (_, es) -> vars_exps acc es
    | Range (e1, Index e2) | BinOp (e1, _, e2) -> vars_exp (vars_exp acc e1) e2
    | Range (e, _) | Reg (e, _) | Memory (e, _) -> vars_exp acc e
    | Coproc_exp (e, _ , es) -> vars_exps (vars_exp acc e) es
    | _ -> acc

  and vars_exps acc es = List.fold_left vars_exp acc es;;

  let rec vars_inst ((gs,ls) as acc) = function
    | Affect (Var s, e) | Affect (Range (Var s, _), e) -> vars_exp
	(if StrMap.mem s gs || StrMap.mem s ls || StrSet.mem s specials
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
    | Case (Var s, nis) ->
        let gs' =
          if StrMap.mem s gs || StrMap.mem s ls || StrSet.mem s specials
	  then gs else StrMap.add s G.key_type gs
        and vars_case acc (_, i) = vars_inst acc i in
	  List.fold_left vars_case (gs', ls) nis
    | _ -> (gs,ls)

  and vars_insts acc is = List.fold_left vars_inst acc is;;

  let vars p = vars_inst (StrMap.empty, StrMap.empty) (prog_inst p);;

end;;

(***********************************************************************)
(** expression preprocessing *)
(***********************************************************************)

let ident i =
  match i.iversion with
    | None -> i.iname
    | Some k -> sprintf "%s%s" i.iname k;;

let  string_of_op = function
  | "+" -> "add"
  | "-" -> "sub"
  | s -> s;;

let func =
  let b = Buffer.create 100 in
    fun ss ->
      Buffer.clear b;
      list "_" string b ss;
      Buffer.contents b;;

(* normalize hexadecimal numbers by using uppercase letters only *)

let hex s =
  let n = String.length s in
    if n <= 2 || String.sub s 0 2 <> "0x" then invalid_arg "Preproc.hex";
    "0x" ^ String.uppercase (String.sub s 2 (n-2));;

(* preprocess expressions *)

let rec exp = function

  (* we only consider ARMv5 and above *)
  | If_exp (Var "v5_and_above", Unaffected, _) -> Unaffected

  (* replace the incorrect function call to R by a register value *)
  | Fun ("R", e :: _) -> Reg (e, None)

  (* rename some function calls depending on the argument,
     and change the argument into a list of arguments,
     e.g. CarrayFrom(a+b) is replaced by CarryFrom_add2(a,b) *)
  | Fun (("OverflowFrom"|"BorrowFrom"|"CarryFrom"|"CarryFrom16"|"CarryFrom8" 
	      as f), [BinOp (_, op, _) as e]) -> let es = args e in
      Fun (sprintf "%s_%s%d" f (string_of_op op) (List.length es),
	   List.map exp es)
  | Fun (("SignExtend_30"|"SignExtend"), ([Var "signed_immed_24"] as es)) ->
      Fun ("SignExtend_24to30", List.map exp es)
(*FIXME: there are other cases for SignExtend *)
  | Fun (("SignedSat"|"UnsignedSat"|"SignedDoesSat"|"UnsignedDoesSat" as f),
         [BinOp (e1, ("+"|"-" as op), e2); Num n]) ->
      Fun (sprintf "%s_%s%s" f (string_of_op op) n, [exp e1; exp e2])
  | Fun (("SignedSat"|"SignedDoesSat" as f),
	 [BinOp (e, "*", Num "2"); Num n]) ->
      Fun (sprintf "%s_double%s" f n, [exp e])

  (* replace English expressions by function calls *)
  | Other ss -> Fun (func ss, [])

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

  (* normalize hexadecimal numbers *)
  | Hex s -> Hex (hex s)

  (* replace "mode" by "CPSR[4:0]" *)
  | Var "mode" -> Range (CPSR, Bits ("4", "0"))

  (* recursive expressions *)
  | Fun (f, es) -> Fun (f, List.map exp es)
  | BinOp (e1, f, e2) -> BinOp (exp e1, f, exp e2)
  | Range (e1, Index e2) -> Range (exp e1, Index (exp e2))
  | Range (e, r) -> Range (exp e, r)
  | If_exp (e1, e2 ,e3) -> If_exp (exp e1, exp e2, exp e3)
  | Memory (e, n) -> Memory (exp e, n)
  | Coproc_exp (e, s, es) -> Coproc_exp (exp e, s, List.map exp es)
  | Reg (e, m) -> Reg (exp e, m)

  (* non-recursive expressions *)
  | (Num _|Bin _|CPSR|SPSR _|Var _|Unaffected|Unpredictable_exp as e) -> e;;

(***********************************************************************)
(** block preprocessing *)
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
      begin match raw_inst i, raw_block is with
	| Block is', is -> is' @ is
	| i, is -> i :: is
      end;;

(***********************************************************************)
(** instruction preprocessing *)
(***********************************************************************)

let nop = Block [];;

let is_nop = (=) nop;;

let lc_decl = ["value"; "operand" ; "operand1" ; "operand2"; "data";
	       "diff1"; "diff2"; "diff3"; "diff4"; "mask"];;

let rec inst = function

  | Block is -> raw_inst (Block (List.map inst is))

  (* replace affectations to Unaffected by nop's *)
  | Affect (e1, e2) -> let e2 = exp e2 in
      begin match e2 with
	| Unaffected -> nop
	| _ -> Affect (exp e1, e2)
      end

  (* we only consider ARMv5 and above *)
  | If (Var "v5_and_above", i, _) -> inst i

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

  (* replace assert's and memory access indications by nop's *)
  | Proc ("MemoryAccess", _) | Assert _ -> nop

  (* replace English expressions by procedure calls *)
  | Misc ss -> Proc (func ss, [])

  (* recursive instructions *)
  | Proc (f, es) -> Proc (f, List.map exp es)
  | While (e, i) -> While (exp e, inst i)
  | For (s, n, p, i) -> For (s, n, p, inst i)
  | Coproc (e, s, es) -> Coproc (exp e, s, List.map exp es)
  | Case (e, s) -> Case (exp e, List.map (fun (n, i) -> (n, inst i)) s)

  (* non-recursive instructions *)
  | Unpredictable -> Unpredictable;;

(***********************************************************************)
(** affectation preprocessing:
- replace affectation of Unpredictable_exp by Unpredictable
- replace conditional affectation of Unpredictable by an equivalent block *)
(***********************************************************************)

let rec affect = function

  | Block is -> raw_inst (Block (List.map affect is))

  | Affect (_, Unpredictable_exp) -> Unpredictable
  | Affect (e1, If_exp (c, Unpredictable_exp, e2)) ->
      Block [If (c, Unpredictable, None); Affect (e1, e2)]

  | If (e, i, None) -> If (e, affect i, None)
  | If (e, i1, Some i2) -> If (e, affect i1, Some (affect i2))
  | While (e, i) -> While (e, affect i)
  | For (s, n, p, i) -> For (s, n, p, affect i)
  | Case (e, s) -> Case (e, List.map (fun (n, i) -> (n, affect i)) s)

  | i -> i;;

(***********************************************************************)
(** program preprocessing *)
(***********************************************************************)

let inst i = affect (inst i);;

let prog = function
  | Instruction (r, id, is, i) -> Instruction (r, id, is, inst i)
  | Operand (r, c, n, i) -> Operand (r, c, n, inst i);;
