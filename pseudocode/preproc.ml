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

module type Gen = sig
  type typ;;
  val local_type : string -> exp -> typ;;
end;;

module Make (G : Gen) = struct

  let set_of_list =
    List.fold_left (fun set s -> StrSet.add s set) StrSet.empty;;

  let input_registers = set_of_list ["n"; "m"; "s"];;
  let output_registers = set_of_list ["d"; "dHi"; "dLo"; "n"];;
  let specials = set_of_list
    ["CP15_reg1_EEbit"; "CP15_reg1_Ubit"; "GE"; "i"; "v5_and_above";
     "UnallocMask"; "StateMask"; "UserMask"; "PrivMask"];;

let rec vars_exp ((gs,ls) as acc) = function
  | Var s ->
      if StrSet.mem s gs || StrMap.mem s ls || StrSet.mem s specials
      then acc
      else StrSet.add s gs, ls
  | If (e1, e2, e3) -> vars_exp (vars_exp (vars_exp acc e1) e2) e3
  | Fun (_, es) -> vars_exps acc es
  | Range (e1, Index e2) | BinOp (e1, _, e2) -> vars_exp (vars_exp acc e1) e2
  | Range (e, _) | Reg (e, _) | Memory (e, _) -> vars_exp acc e
  | Coproc_exp (e, _ , es) -> vars_exps (vars_exp acc e) es
  | _ -> acc

and vars_exps acc es = List.fold_left vars_exp acc es;;

let rec vars_inst ((gs,ls) as acc) = function
    | Affect (Var s, e) | Affect (Range (Var s, _), e) -> vars_exp
	(if StrSet.mem s gs || StrMap.mem s ls || StrSet.mem s specials
	 then acc
	 else
	   if StrSet.mem s output_registers
	   then StrSet.add s gs, ls
	   else gs, StrMap.add s (G.local_type s e) ls) e
    | Block is -> vars_insts acc is
    | IfThenElse (e, i, None) | While (e, i) -> vars_inst (vars_exp acc e) i
    | IfThenElse (e, i1, Some i2) ->
	vars_inst (vars_inst (vars_exp acc e) i1) i2
    | Proc (_, es) -> vars_exps acc es
    | For (_, _, _, i) -> vars_inst acc i
    | Affect (e1, e2) -> vars_exp (vars_exp acc e1) e2
    | Coproc(e, _ , es) -> vars_exps (vars_exp acc e) es
    | _ -> (gs,ls)

and vars_insts acc is = List.fold_left vars_inst acc is;;

let vars p = vars_inst (StrSet.empty, StrMap.empty) p.pinst;;

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

let rec exp p =
  let rec exp = function
    | If (Var "v5_and_above", Unaffected, UnpredictableValue) -> Unaffected
    | If (e1, e2 ,e3) -> If (exp e1, exp e2, exp e3)
    | Fun ("R", e :: _) -> Reg (e, None)
    | Fun (("OverflowFrom"|"BorrowFrom"
	   |"CarryFrom"|"CarryFrom16"|"CarryFrom8" as f),
	   [BinOp (_, op, _) as e]) -> let es = args e in
	Fun (sprintf "%s_%s%d" f (string_of_op op) (List.length es), es)
    | Fun (("SignExtend_30"|"SignExtend"), ([Var "signed_immed_24"] as es)) ->
        Fun ("SignExtend_24to30", es)
    | Fun (("SignedSat"|"UnsignedSat"|"SignedDoesSat"|"UnsignedDoesSat" as f),
           [BinOp (e1, ("+"|"-" as op), e2); Num n]) ->
        Fun ((sprintf "%s_%s%s" f (string_of_op op) n), [exp e1; exp e2])
    | Fun ("SignedSat"|"SignedDoesSat" as f,
           [BinOp (e, "*", Num "2"); Num n]) ->
        Fun ((sprintf "%s_double%s" f n), [exp e])
    | Fun (f, es) -> Fun (f, List.map exp es)
    | BinOp (e, ("==" as f), Reg (n, None)) -> BinOp (exp e, f, n)
    | BinOp (e1, f, e2) -> BinOp (exp e1, f, exp e2)
    | Other ss -> Fun (func ss, [])
    | Range (e, r) -> Range (exp e, range p r)
    | UnpredictableValue ->
	Fun (sprintf "%s_UnpredictableValue" (ident p.pident), [])
    | e -> e
  in exp

and range p = function
  | Index e -> Index (exp p e)
  | r -> r;;

let nop = Block [];;

let is_nop = (=) nop;;

let remove_nops = List.filter ((<>) nop);;

let inst p =
  let exp = exp p in
  let rec inst = function
    | Block [i] -> inst i
    | Block is -> Block (remove_nops (List.map inst is))
    | Unpredictable -> Unpredictable
    | Affect (e1, e2) -> let e2 = exp e2 in
	if e2 = Unaffected then nop else Affect (exp e1, e2)
    | IfThenElse (e, i, None) ->
	let i = inst i in
	  if is_nop i then nop else IfThenElse (exp e, i, None)
    | IfThenElse (e, i1, Some i2) ->
	let i2 = inst i2 in
	  if is_nop i2 then IfThenElse (exp e, inst i1, None)
	  else IfThenElse (exp e, inst i1, Some (inst i2))
    | Proc ("MemoryAccess", _) -> nop
    | Proc (f, es) -> Proc (f, List.map exp es)
    | While (e, i) -> While (exp e, inst i)
    | Assert _ -> nop
    | For (s, n, p, i) -> For (s, n, p, inst i)
    | Misc ss -> Proc (func ss, [])
    | Coproc (e, s, es) -> Coproc (exp e, s, List.map exp es)
  in inst

let prog p = {p with pinst = inst p p.pinst};;
