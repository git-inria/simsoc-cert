(**
SimSoC-Cert, a library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Generator of the instruction decoder for Coq.
*)

open Ast;;
open Printf;;
open Util;;
open Codetype;;

(*type lightheader = LH of int list * string

type pos_contents = 
  | Nothing
  | Value of bool                  (* false -> 0, true -> 1 *)
  | Param1 of char                 (* e.g. S *)
  | Param1s of string              (* e.g. mmod *)
  | Range of string * int * int    (* length position, e.g. Rn 4 0 *)
  | Shouldbe of bool               (* false -> SBZ, true -> SBO *)

type maplist = (lightheader * pos_contents array) list 
*)

let lightheader b p =
  match p with LH (is, s)
  -> bprintf b "%a%s" (list "" int) is s;;

let comment b lh = bprintf b "(*%a*)" lightheader lh;;

(*TODO : change the names of addressing mode instructions*)
let inst_name b p =
    match p with LH (_, s)
    -> bprintf b "%s" s;;

(*TODO : add bit x y*)
let dec b pc =
    match pc with
      | Value s -> 
	  begin match s with
	    | true -> bprintf b "1"
	    | false -> string b "0"
	  end 
      | Shouldbe s -> 
	  begin match s with
	    | true -> string b "1"
	    | false -> string b "0"
	  end
      | Param1 s -> bprintf b "%c" s
      | Param1s _ -> string b "_"
      | Range _ -> string b "_"
      | Nothing -> ();;

(*TODO : arguments order*)
(*TODO : bit 'I' is not an argument in data processing instructions*)
(*TODO : blank between arguments*)

let inst_param b ps =
    match ps with
      | (Range (("Rs"| "Rm" | "Rn" | "Rd" | "CRd" | "CRm"| "CRn"),_ ,_), i) ->
	  bprintf b "(reg_num_from bit %d w)" i
      | (Range ("shifter_operand", _, _), _) -> 
	  string b "(decode_shifter_operand w I y)"
      | (Range (("immed_24"| "signed_immed_24"), _, _), _) ->
	  string b "(signed_immed_24 w)"
      | (Range ("cond", _, _), _) -> string b "(cond w)"
      | (Range (_, i1, _), i) -> bprintf b "w[%d#%d]" (i+i1-1) i
      | (Param1s s, _) -> bprintf b "%s " s
      | (Param1 c, _) -> bprintf b "%c" c
      | ((Value _ | Shouldbe _ | Nothing) , _)
	  -> ()
 ;;

let param_m ar =
  let res = Array.create (Array.length ar) (Nothing,0) in
    for i = 0 to (Array.length ar -1) do
      res.(i) <- (ar.(i), i)
    done;
    for i = 0 to (Array.length ar -1) do
      match res.(i) with
	| (Range (_, len, _),_) ->
	    for j = 1 to len-1 do
	      res.(i+j) <- (Nothing, i+j)
	    done;
	| ((Param1 _ | Value _ | Shouldbe _ | Nothing | Param1s _),_) ->
	    res.(i) <- res.(i)
    done;
    res;;

let params f x =
  let aux b =
    let lst = Array.to_list (param_m x) in
      (list "" f) b lst
  in aux;;

let bits f x =
  let aux b =
    let lst = Array.to_list x in
      (list " '" f) b (List.rev lst)
  in aux;;
    
let dec_inst b (lh, ls) =
  bprintf b
    "    %a\n    | %t =>\n      Inst (%a %t)\n"
    comment lh (bits dec ls) inst_name lh (params inst_param ls);
;;
(*TODO : add the definition begin and end*)

let decode =
  list "" dec_inst;;
