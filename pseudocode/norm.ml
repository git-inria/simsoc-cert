(**
SimSoC-Cert, a library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Pseudocode normalization: transform an AST into another AST
better suited for code generation in a functional language.
*)

open Ast;;
open Printf;;
open Util;;

(*****************************************************************************)
(** normalization of expressions *)
(*****************************************************************************)

let string_of_op = function
  | "+" -> "add"
  | "-" -> "sub"
  | s -> s;;

let size = function
  | Range (_, Bits (("15"|"31"), _)) -> "16"
  | _ -> "8";;

let rec exp = function

  (* we only consider ARMv5 and above *)
  | If_exp (Fun ("v5_and_above", []), e, _) -> exp e

  (* normalize ranges *)
  | Range (e1, Index e2) -> range (exp e1) (Index (exp e2))
  | Range (e, r) -> range (exp e) r

  (* rename calls to SignExtend depending on the size of the argument *)
  | Fun ("SignExtend" as f, (e :: _ as es)) -> Fun (f ^ size e, es)
 
  (* rename calls to *From depending on the argument,
     and change the argument into a list of arguments,
     e.g. CarrayFrom(a+b) is replaced by CarryFrom_add2(a,b) *)
  | Fun (("OverflowFrom"|"BorrowFrom"|"CarryFrom"|"CarryFrom8"|"CarryFrom16"
	      as f), (BinOp (_, op, _) as e) :: _) -> let es = args e in
      Fun (sprintf "%s_%s%d" f (string_of_op op) (List.length es),
	   List.map exp es)

  (* normalize if-expressions wrt Unpredictable_exp's: if-expressions
     are flattened so that there is at most one Unpredictable_exp in the
     then-branch *)
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
  |Num _|Bin _|Hex _|CPSR|SPSR _|Var _|Unaffected|Unpredictable_exp as e -> e

(* replace two successive ranges by a single one *)
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

(*****************************************************************************)
(** normalization of blocks:
blocks are flattened and removed if they reduce to a single instruction *)
(*****************************************************************************)

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

(*****************************************************************************)
(** normalization of instructions (1st pass):
an instruction is replaced by at most one instruction *)
(*****************************************************************************)

let nop = Block [];;

let is_nop = (=) nop;;

(* variables used as local variables *)
let locals = set_of_list
  ["value"; "operand" ; "operand1" ; "operand2"; "data"; "mask";
   "diff1"; "diff2"; "diff3"; "diff4"; "shifter_operand"; "shifter_carry_out";
   "address"; "start_address"; "index"];;

let is_local = function
  | Var x (*REMOVE?| Fun (x, [])*) -> StrSet.mem x locals
  | _ -> false;;

let eq_local e1 e2 =
  match e1, e2 with
    | Var x1, Var x2 (*REMOVE?| Fun (x1, []), Fun (x2, [])*) ->
	x1 = x2 && StrSet.mem x1 locals
    | _, _ -> false;;

let rec inst = function

  (* we only consider ARMv5 and above *)
  | If (Fun ("v5_and_above", []), i, _) -> inst i

  (* replace assert's and memory access indications by nop's *)
  | Proc ("MemoryAccess", _) | Assert _ -> nop

  (* normalize block's *)
  | Block is -> raw_inst (Block (List.map inst is))

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
	  then If (Fun ("not", [exp c]), i2, None)
	  else

	    (* normalization of affectations for local variables: if
	       both branches of an if-instruction affect the same
	       variable, then it is converted into a single affectation
	       which value is defined with an if-expression *)
	    begin match i1, i2 with
	      | Affect (x1, e1), Affect (x2, e2) when eq_local x1 x2 ->
		  inst (Affect (x1, If_exp (c, e1, e2)))
	      | Affect (x, e), Unpredictable when is_local x ->
		  inst (Affect (x, If_exp (c, e, Unpredictable_exp)))
	      | Unpredictable, Affect (x, e) when is_local x ->
		  inst (Affect (x, If_exp (c, Unpredictable_exp, e)))

	      (* case of two affectations *)
	      | Block [Affect (x1, u1); Affect (y1, v1)],
		Block [Affect (x2, u2); Affect (y2, v2)]
		  when eq_local x1 x2 && eq_local y1 y2 ->
		  inst (Block
			  [Affect (x1, If_exp (c, u1, u2));
			   Affect (y1, If_exp (c, v1, v2))])

	      | _ -> If (exp c, i1, Some i2)
	    end

  (* recursive instructions *)
  | Proc (f, es) -> Proc (f, List.map exp es)
  | While (e, i) -> While (exp e, inst i)
  | For (s, n, p, i) -> For (s, n, p, inst i)
  | Coproc (e, s, es) -> Coproc (exp e, s, List.map exp es)
  | Case (e, s) -> Case (exp e, List.map (fun (n, i) -> (n, inst i)) s)

  (* non-recursive instructions *)
  | Unpredictable as i -> i;;

(*****************************************************************************)
(** normalization of affectations (2nd pass):
- replace affectation of Unpredictable_exp by Unpredictable
- replace conditional affectation of Unpredictable by an equivalent block *)
(*****************************************************************************)

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

  (* adhoc treatment of the affectation of a 64-bits word
     with two 32-bits affectations *)
  | Affect (Range (Var x1 as x, Bits ("31", "0")), e1) ::
    Affect (Range (Var x2, Bits ("63", "32")), e2) :: is when x1 = x2 ->
      let e1 = Fun ("ZeroExtend", [e1]) and e2 = Fun ("ZeroExtend", [e2]) in
	Affect (x, BinOp (BinOp (e2, "<<", Num "32"), "OR", e1)) :: affects is

  | i :: is ->
      begin match affect i with
	| Block is' -> is' @ affects is
	| i -> i :: affects is
      end;;

(*****************************************************************************)
(** normalization of programs *)
(*****************************************************************************)

let prog p = { p with pinst = affect (inst p.pinst) };;
