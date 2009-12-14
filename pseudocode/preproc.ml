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

let name p =
  match p.pversion with
    | None -> p.pname
    | Some k -> sprintf "%s%s" p.pname k;;

(***********************************************************************)
(** program preprocessing *)
(***********************************************************************)

let args =
  let rec args = function
    | BinOp (e1, _, e2) -> e2 :: args e1
    | e -> [e]
  in fun es -> List.rev (args es);;

let  string_of_op = function
  | "+" -> "add"
  | s -> s;;

let func p ss =
  let b = Buffer.create 100 in
    bprintf b "%s_" (name p);
    let f = Str.global_replace (Str.regexp "[][',]") "" in
    Util.list "_" (fun b s -> Util.string b (f s)) b ss;
    Buffer.contents b;;

let rec exp p =
  let rec exp = function
    | If (Var "v5_and_above", Unaffected, UnpredictableValue) -> Unaffected
    | If (e1, e2 ,e3) -> If (exp e1, exp e2, exp e3)
    | Fun (("CarryFrom"|"OverflowFrom" as f), [BinOp (_, op, _) as e]) ->
	let es = args e in
	  Fun (sprintf "%s_%s%d" f (string_of_op op) (List.length es), es)
    | Fun (f, es) -> Fun (f, List.map exp es)
    | BinOp (e1, f, e2) -> (*Fun (f, List.map exp [e1; e2])*)
	BinOp (exp e1, f, exp e2)
    | Other ss -> Fun (func p ss, [])
    | Range (e, r) -> Range (exp e, range p r)
    | Unaffected ->
	invalid_arg (sprintf "preprocessing Unaffected in %s" (name p))
    | UnpredictableValue -> Fun (sprintf "%s_UnpredictableValue" (name p), [])
    | e -> e
  in exp

and range p = function
  | Index es -> Index (List.map (exp p) es)
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
    | Affect (_, Unaffected) -> nop
    | Affect (e1, e2) -> Affect (exp e1, exp e2)
(*    | IfThenElse (Fun ("CurrentModeHasSPSR", []), Affect (CPSR, SPSR None),
		  Some Unpredictable) -> *)
    | IfThenElse (e, i, None) ->
	let i = inst i in
	  if is_nop i then nop else IfThenElse (exp e, i, None)
    | IfThenElse (e, i1, Some i2) ->
	let i2 = inst i2 in
	  if is_nop i2 then IfThenElse (exp e, inst i1, None)
	  else IfThenElse (exp e, inst i1, Some (inst i2))
    | Proc (("CarryFrom"|"OverflowFrom" as f), [e]) ->
	let es = args e in
	  Proc (sprintf "%s_%s%d" f (name p) (List.length es), es)
    | Proc (f, es) -> Proc (f, List.map exp es)
    | While (e, i) -> While (exp e, inst i)
    | Assert e -> Assert (exp e)
    | For (s, n, p, i) -> For (s, n, p, inst i)
    | Misc ss -> Proc (func p ss, [])
  in inst

let prog p = {p with pinst = inst p p.pinst};;
