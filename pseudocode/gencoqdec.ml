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
(*
type lightheader = LH of int list * string

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
  -> bprintf b "%a - %s" (list "." int) is s;;

let comment b lh = bprintf b "(*%a*)" lightheader lh;;

let str_to_lst s =
  Str.split (Str.regexp "[-:<>() \t]+") s;;

let name_lst (lh,_) =
  match lh with
    | LH (_, "B, BL") -> ["B"]
    | LH (_, s) ->
	str_to_lst s;;

let rec underscore = function
  | [] -> ""
  | [s] -> s
  | s :: ss -> s ^ "_" ^ underscore ss;;

type kind =
  | Addr_mode of int
  | Inst
  | Encoding;;

let add_mode ss =
  match ss with
    | "Encoding" :: _ -> Encoding
    | "Data" :: _ -> Addr_mode 1
    | "Miscellaneous" :: _ -> Addr_mode 3
    | _ :: _ :: _ :: m :: _ ->
	begin match m with
	  | "Word" -> Addr_mode 2
	  | "Multiple" -> Addr_mode 4
	  | "Coprocessor" -> Addr_mode 5
	  | _ -> Addr_mode 0
	end
    | _ -> Inst;;

let short_name ss =
  match ss with
    | "Data" :: "processing" :: "operands" :: s -> s
    | "Load" :: "and" :: "Store" :: "Word" :: "or" :: "Unsigned" :: "Byte" :: s -> s
    | "Miscellaneous" :: "Loads" :: "and" :: "Stores" :: s -> s
    | "Load" :: "and" :: "Store" :: "Multiple" :: s -> s
    | "Load" :: "and" :: "Store" :: "Coprocessor" :: s -> s
    | _ -> ss;; 


let name ss =
  let md = add_mode ss in
    match md with
      | Addr_mode i -> (Printf.sprintf "M%d" i) :: (short_name ss)
      | Inst -> ss
      | Encoding -> ss;;

let id ps =  underscore (name (name_lst ps));;

let pos_info pc =
  let ar = Array.create (Array.length pc) (Nothing, 0) in
    for i = 0 to Array.length pc - 1 do
      ar.(i) <- (pc.(i), i)
    done;
    ar;;

let dec b pc =
  match pc with
    | (Value s, _) -> 
	begin match s with
	  | true -> string b "1"
	  | false -> string b "0"
	end 
    | (Shouldbe s, i) -> 
	begin match s with
	  | true -> bprintf b "SBO%d" i 
	  | false -> bprintf b "SBZ%d" i
	end
    | (Param1 c, _) -> bprintf b "%s_"  (Char.escaped c)
    | (Param1s s, _) -> bprintf b "%s" s
    | (Range _, _) -> string b "_"
    | (Nothing, _) -> ()
;;

let mode_var m lst =
  let l = List.map (fun (s,_,_) -> s) lst in
  let n = List.hd m in
  let mode3 = ["LDRD";"LDRH";"LDRSB";"LDRSH";"STRD";"STRH"] in
  let mode4 = ["RFE";"SRS"] in
  let mode5 = ["LDC";"STC"] in
    if (List.mem "shifter_operand" l) then 1
    else if (List.mem "register_list" l) then 4
    else if (List.mem "addr_mode" l) then 
      if (List.mem n mode3) then 3 else 2
    else if (List.mem n mode4) then 4
    else if (List.mem n mode5) then 5
    else 0;;

let add_mode_var n lst =
    if (mode_var n lst != 0) then
      let v = Printf.sprintf "i%d" (mode_var n lst) in
	List.append [(v, 0, 0)] lst
    else lst;;

let not_var1 i =
  match i with
    | 1 -> ["S"; "cond"; "d"; "n"; "opcode"]
    | 2 -> ["B"; "L"; "cond"; "d"; "H"; "S"]
    | 3 -> ["B"; "L"; "cond"; "d"; "H"; "S"]
    | 4 -> ["L"; "S"; "CRd"; "N"; "option"; "i4"]
    | 5 -> ["L"; "U"; "S" ; "CRd"; "N"; "option"]
    | _ -> [];;

let not_var2 i =
  match i with
    | 1 -> ["shifter_operand"; "I_"]
    | 2 -> ["P"; "U"; "W"; "addr_mode"]
    | 3 -> ["I"; "P"; "W"; "U"; "Rn"; "addr_mode"]
    | 4 -> ["P"; "U"; "W"; "Rn"]
    | 5 -> ["8_bit_word_offset"; "CRd"; "P"; "U"; "W"]
    | _ -> [];;

let not_var n =
    match n with
      | ("MRC"|"CDP")::_ -> ["opcode_1"; "opcode_2"; "CRd"; "CRm"; "CRn"]
      | _ -> [];;

let is_not_var1 i =
  fun (s, _, _) -> List.mem s (not_var1 i);;

let is_not_var2 i =
  fun (s, _, _) -> List.mem s (not_var2 i);;

let remove_var n lst = 
  let im = mode_var n lst in
  let md = add_mode n in
    List.map (fun s -> if (
		match md with
		  | Addr_mode i -> is_not_var1 i s
		  | Inst -> is_not_var2 im s
		  | Encoding -> false) then
		("",0,0) else s) lst;;

let remove_vars n lst =
  let md = add_mode n in
    match md with
      | (Addr_mode _ | Inst) -> remove_var n lst
      | Encoding -> lst;;

let inst_param ls =
  match ls with
    | (("s" | "m" | "n" | "d" | "dHi" | "dLo"), i, _) ->
	Printf.sprintf "(regnum_from_bit %d w)" i
    | ("shifter_operand", _, _) ->
	"(decode_shifter_operand w I x)"
    | ("cond", _, _) ->
	"(condition w)"
    | (s, p, l) -> 
	if l > 1 then 
	  Printf.sprintf "w[%d#%d]" (p+l-1) p
	else
	  Printf.sprintf "%s" s
;;

let param_m ar =
  let res = Array.create (Array.length ar) ("", 0, 0) in
    for i = 0 to (Array.length ar -1) do
      match ar.(i) with
	| Range (s, len, _) ->
	    if s.[0] = 'R' then
	      res.(i) <- ((String.sub s 1 (String.length s -1)), i, len)
	    else
	      res.(i) <- (s, i, len)
	| (Nothing | Value _ | Shouldbe _) -> 
	    res.(i) <- ("", 0, 0)
	| Param1 c -> 
	    res.(i) <-  ((Printf.sprintf "%s_" (Char.escaped c)), i, 1)
	| Param1s s -> 
	    res.(i) <- (s, i, 1)
    done;
    for i = 0 to (Array.length ar -1) do
    match res.(i) with
      | ("immed", _, _) ->
	  res.(i) <- ("", 0, 0)
      | ("I", 25, _) -> 
	  res.(i) <- ("", 0, 0)
      | (_, _, len) ->
	  if len > 0 then
	  for j = 1 to len -1 do
	    res.(i + j) <- ("", 0, 0)
	  done;
	  done;
    res;;

let params f (lh, ls) =
  let dname = name (name_lst (lh,ls)) in
  let n = name_lst (lh, ls) in
  let aux b =
    let lst =
	(List.filter ((<>) "")
	      (List.map inst_param
		 (remove_vars n
		    (add_mode_var dname
		       (List.sort (fun (s1, _, _) (s2, _, _) -> 
				     Pervasives.compare s1 s2)
			  (Array.to_list (param_m ls)))))))
    in
      (list " " f) b lst
  in aux;;

let sbo_tst ls =
  match ls with
    | (Shouldbe true, i) -> Printf.sprintf "SBO%d" i
    | ((Nothing | Value _ | Param1 _ | Param1s _ | Range _ | Shouldbe false), _)
      -> "";;

let sbz_tst ls =
  match ls with
    | (Shouldbe false, i) -> Printf.sprintf "SBZ%d" i
    | ((Nothing | Value _ | Param1 _ | Param1s _ | Range _ | Shouldbe true), _)
      -> "";;

let shouldbe_test (lh, ls) =
  let lst = Array.to_list ls in
  let ps = Array.to_list (pos_info ls) in
  let sbo = List.filter ((<>) "") (List.map sbo_tst ps) in
  let sbz = List.filter ((<>) "") (List.map sbz_tst ps) in
  let aux b =
    if ((List.mem (Shouldbe true) lst) && (not (List.mem (Shouldbe false) lst))) then
      bprintf b "if (%a) then\n      DecInst (%s %t)\n      else DecUnpredictable"
	(list "&&" string) sbo (id (lh,ls)) (params string (lh, ls))
    else 
      if (List.mem (Shouldbe false) lst && (not (List.mem (Shouldbe true) lst))) then
	bprintf b "if (not (%a)) then \n      DecInst (%s %t)\n      else DecUnpredictable"
	  (list "&&" string) sbz (id (lh,ls)) (params string (lh, ls))
      else 
	if (List.mem (Shouldbe false) lst && (List.mem (Shouldbe true) lst)) then
	  bprintf b "if ((%a) && (not (%a))) then \n      DecInst (%s %t)\n      else DecUnpredictable"
	 (list "&&" string) sbo (list "&" string) sbz (id (lh,ls)) (params string (lh, ls))
	else
	  bprintf b "DecInst (%s %t)" (id (lh,ls)) (params string (lh, ls))
  in aux;;

let mode_tst (lh, ls) =
  let aux b =
  let lst = Array.to_list (param_m ls) in
  let md = mode_var (name_lst (lh, ls)) lst in
  match md with
    | (1|2|3|4|5 as i) -> bprintf b "match (decode_addr_mode%d w) with\n        | DecInst i%d =>\n            %t\n        | _ => i%d\n      end" i i (shouldbe_test (lh, ls)) i
    | _ -> bprintf b "%t" (shouldbe_test (lh, ls))
  in aux;;

let bits f x =
  let aux b =
    let lst = Array.to_list x in
      (list " '" f) b (List.rev lst)
  in aux;;

let dec_inst b (lh, ls) =
  let dbits = pos_info ls in
    let md = add_mode (name_lst (lh,ls)) in
      match md with
	| Inst -> 
	    bprintf b "    %a\n    | %t =>\n      %t\n"
	      comment lh (bits dec dbits) (mode_tst (lh, ls))
	| Encoding -> ()
	| Addr_mode _ -> 
	    bprintf b "    %a\n    | %t =>\n      DecInst (%s %t)\n"
	      comment lh (bits dec dbits)
	      (id (lh, ls)) (params string (lh, ls))
;;



let is_inst l =
  if ((add_mode (name_lst l)) = Inst) then true else false;;

let is_addr_mode i l =
  if ((add_mode (name_lst l)) = Addr_mode i) then true else false;;

let decode b ps =
  string b "Require Import Bitvec List Util Functions Config Arm State Semantics ZArith arm6inst Simul String.\n\nOpen Scope string_scope.\n\nLocal Notation \"0\" := false.\nLocal Notation \"1\" := true.\nLocal Infix \"\'\" := cons (at level 60, right associativity).";
  for i = 1 to 5 do
    bprintf b "\n\nDefinition decode_addr_mode%d (w : word) : decoder_result mode%d:=\n match bools_of_word w with\n" i i;
  (list "" dec_inst) b (List.filter (is_addr_mode i) ps);
  bprintf b "    | _ => DecError mode%d \"not a addressing mode %d\"\n  end." i i
  done;
  bprintf b "\n\nDefinition decode (w : word) : decoder_result inst :=\n  match bools_of_word w with\n";
  (list "" dec_inst) b (List.filter (is_inst) ps);
  bprintf b "    | _ => DecUndefined\n  end."
;;
