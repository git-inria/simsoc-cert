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

  let set_of_list =
    List.fold_left (fun set s -> StrSet.add s set) StrSet.empty;;

  let input_registers = set_of_list ["n"; "m"; "s"];;
  let output_registers = set_of_list ["d"; "dHi"; "dLo"; "n"];;
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
    | Block is -> vars_insts acc is
    | If (e, i, None) | While (e, i) -> vars_inst (vars_exp acc e) i
    | If (e, i1, Some i2) ->
	vars_inst (vars_inst (vars_exp acc e) i1) i2
    | Proc (_, es) -> vars_exps acc es
    | For (_, _, _, i) -> vars_inst acc i
    | Affect (e1, e2) -> vars_exp (vars_exp acc e1) e2
    | Coproc(e, _ , es) -> vars_exps (vars_exp acc e) es
    | Case (Var v, s) ->
        let gs' =
          if StrMap.mem v gs || StrMap.mem v ls || StrSet.mem v specials
	  then gs else StrMap.add v G.key_type gs
        and vars_case acc (_, i) = vars_inst acc i
        in List.fold_left vars_case (gs', ls) s
    | _ -> (gs,ls)

and vars_insts acc is = List.fold_left vars_inst acc is;;

let vars p = vars_inst (StrMap.empty, StrMap.empty) (inst_of p);;

end;;

(***********************************************************************)
(** program preprocessing *)
(***********************************************************************)

let ident i =
  match i.iversion with
    | None -> i.iname
    | Some k -> sprintf "%s%s" i.iname k;;

let  string_of_op = function
  | "+" -> "add"
  | "-" -> "sub"
  | s -> s;;

let func ss =
  let b = Buffer.create 100 in
    list "_" string b ss;
    Buffer.contents b;;

let rec exp = function

  (* we only consider ARMv5 and above *)
  | If_exp (Var "v5_and_above", Unaffected, _) -> Unaffected

  (* replace the incorrect function call to R by a register value *)
  | Fun ("R", e :: _) -> Reg (e, None)

  (* rename some function calls depending on the argument,
     and change the argument into a list of arguments,
     e.g. CarrayFrom(a+b) is replaced by CarryFrom_add2(a,b) *)
  | Fun (("OverflowFrom"|"BorrowFrom"
	 |"CarryFrom"|"CarryFrom16"|"CarryFrom8" as f),
	 [BinOp (_, op, _) as e]) -> let es = args e in
      Fun (sprintf "%s_%s%d" f (string_of_op op) (List.length es),
	   List.map exp es)
  | Fun (("SignExtend_30"|"SignExtend"), ([Var "signed_immed_24"] as es)) ->
      Fun ("SignExtend_24to30", List.map exp es)
  | Fun (("SignedSat"|"UnsignedSat"|"SignedDoesSat"|"UnsignedDoesSat" as f),
         [BinOp (e1, ("+"|"-" as op), e2); Num n]) ->
      Fun (sprintf "%s_%s%s" f (string_of_op op) n, [exp e1; exp e2])
  | Fun (("SignedSat"|"SignedDoesSat" as f),
	 [BinOp (e, "*", Num "2"); Num n]) ->
      Fun (sprintf "%s_double%s" f n, [exp e])

  (* replace English expressions by function calls *)
  | Other ss -> Fun (func ss, [])

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
  | (Num _|Bin _|Hex _|CPSR|SPSR _|Var _|Unaffected|Unpredictable_exp as e) ->
      e;;

let nop = Block [];;

let is_nop = (=) nop;;

let remove_nops = List.filter ((<>) nop);;

let rec inst = function

  (* remove blocks reduced to one instruction *)
  | Block is ->
      begin match remove_nops (List.map inst is) with
	| [i] -> i
	| is -> Block is
      end

  (* replace affectations to Unaffected by nop's *)
  | Affect (e1, e2) -> let e2 = exp e2 in
      if e2 = Unaffected then nop else Affect (exp e1, e2)

  (* we only consider ARMv5 and above *)
  | If (Var "v5_and_above", i, _) -> inst i

  (* simplify conditional instructions wrt nop's *)
  | If (e, i, None) ->
      let i = inst i in
	if is_nop i then nop else If (exp e, i, None)
  | If (e, i1, Some i2) ->
      let i1 = inst i1 and i2 = inst i2 in
	if is_nop i2 then
	  if is_nop i1
	  then nop
	  else If (exp e, i1, None)
	else
	  if is_nop i1
	  then If (Fun ("NOT", [exp e]), i2, None)
	  else If (exp e, i1, Some i2)

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

let prog = function
  | Instruction (r, id, is, i) -> Instruction (r, id, is, (inst i))
  | Operand (r, c, n, i) -> Operand (r, c, n, (inst i));;
