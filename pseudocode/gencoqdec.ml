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


(*****************************************************************************)
(** comment *)
(*****************************************************************************)

let lightheader b p =
  match p with LH (is, s)
  -> bprintf b "%a - %s" (list "." int) is s;;

let comment b lh = bprintf b "(*%a*)" lightheader lh;;

(*****************************************************************************)
(** rearrange the name *)
(*****************************************************************************)

(*convert the name string to list*)
let str_to_lst s =
  Str.split (Str.regexp "[-:<>() \t]+") s;;

(*organise the input data with different types*)
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

(*catch the number of instruction*)
let num (lh, _) =
  match lh with LH (is, _) -> List.nth is 1;;

(*add/remove underscore between the strings of name list*)
let rec underscore = function
  | [] -> ""
  | [s] -> s
  | s :: ss -> s ^ "_" ^ underscore ss;;

let rec remove_underscore = function
  | [] -> ""
  | [s] -> s
  | s :: ss -> s ^ remove_underscore ss;;

(*rename B,BL and MSR*)
let name_lst (lh,_) =
  match lh with
    | LH (_, "B, BL") -> ["B"]
    | LH (_, "MSR  Immediate operand:") -> ["MSR"]
    | LH (_, "MSR  Register operand:") -> ["MSR"]
    | LH (_, s) ->
	str_to_lst s;;

(*rename addressing modes*)
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
let id_inst ps =  remove_underscore (name (name_lst ps));;

(*****************************************************************************)
(** binary list *)
(*****************************************************************************)

(*add the position of element in the array*)
let pos_info pc =
  let ar = Array.create (Array.length pc) (Nothing, 0) in
    for i = 0 to Array.length pc - 1 do
      ar.(i) <- (pc.(i), i)
    done;
    ar;;

(*translate array content to binary and variable*)
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
    | (Param1 c, _) -> bprintf b "%c_" c (*REMOVE: (Char.escaped c)*)
    | (Param1s s, _) -> bprintf b "%s" s
    | (Range _, _) -> string b "_"
    | (Nothing, _) -> ()
;;

(*print the bit list and separated by '*)
let bits f x =
  let aux b =
    let lst = Array.to_list x in
      (list " '" f) b (List.rev lst)
  in aux;;

(*****************************************************************************)
(** add addressing mode infomation to instructions *)
(*****************************************************************************)

(*set instruction with address mode according to name and parameter*)
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

(*add address mode variable in the parameter list*)
let add_mode_var n lst =
    if (mode_var n lst != 0) then
      (*REMOVE:let v = Printf.sprintf "i%d" (mode_var n lst) in*)
	List.append [("i", 0, 0)] lst
    else lst;;

(*****************************************************************************)
(** parameters of operation function *)
(*****************************************************************************)

(*remove the unused one from the parameter list
 according to addressing mode*)
let not_var1 i =
  match i with
    | 1 -> ["S_"; "cond"; "d"; "n"; "opcode"]
    | 2 -> ["B_"; "L_"; "d"; "H_"; "S_"]
    | 3 -> ["B_"; "L_"; "d"; "H_"; "S_"]
    | 4 -> ["L_"; "S_"; "CRd"; "N_"; "option"; "i4"]
    | 5 -> ["L_"; "S_" ; "CRd"; "N_"; "option"]
    | _ -> [];;

let not_var2 i =
  match i with
    | 1 -> ["shifter_operand"; "I_"]
    | 2 -> ["P_"; "U_"; "W_"; "addr_mode"; "I_"]
    | 3 -> ["I_"; "P_"; "W_"; "U_"; "n"; "addr_mode"]
    | 4 -> ["P_"; "U_"; "W_"; "n"; "mode"]
    | 5 -> ["8_bit_word_offset"; "CRd"; "P_"; "U_"; "W_"; "N_"; "n"]
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
		  | Inst ->
		      is_not_var2 im s
		  | Encoding -> false) then
		("",0,0) else s) lst;;

let remove_vars n lst =
  let md = add_mode n in
    match md with
      | (Addr_mode _ | Inst) -> remove_var n lst
      | Encoding -> lst;;

(*remove variable in other cases*)
let remove_var_cond n lst =
  match n with
    | ("M2" ::_ :: "offset" :: _ |"M2" ::_ :: _ :: "offset" :: _ | "M3" :: _ :: "offset" :: _) ->
	List.map (fun (s, i1, i2) -> 
		    if (s = "cond") then ("",0,0) else (s, i1, i2)) lst
    | ("MRC"|"MCR"|"MCRR"|"CDP"|"MRRC")::_ ->
	List.map (fun (s, i1, i2) -> 
		    if (s = "opcode_1")||(s = "opcode_2")||(s ="CRd")||(s = "CRm")||(s = "CRn")||(s = "opcode") then ("",0,0) else (s, i1, i2)) lst
    | "M3" :: "Register" :: _ ->
	List.map (fun (s, i1, i2) -> 
		    if (s = "immedL")||(s = "immedH") then ("",0,0) else (s, i1, i2)) lst
    | "M5" :: "Unindexed" :: _ ->
	List.map (fun (s, i1, i2) -> if (s = "U_") then ("",0,0) else (s, i1, i2)) lst
    | "MSR" :: _ -> List.map (fun (s, i1, i2) -> if (s = "field_mask")||(s = "cond")||(s = "m")||(s = "8_bit_immediate")||(s = "rotate_imm")||(s = "R_") then 
				("",0,0) else (s, i1, i2)) lst
    | "SWI" :: _ -> List.map (fun (s, i1, i2) -> if (s = "immed_24") then ("",0,0) else (s, i1, i2)) lst
    | ("LDRB"|"STRB"|"LDR"|"STR"|"STRBT"|"LDRT"|"STRT"|"SWPB"|"SWP") :: _ -> List.map (fun (s, i1, i2) -> if (s = "n") then ("",0,0) else (s, i1, i2)) lst
    | ("PLD") :: _ -> List.map (fun (s, i1, i2) -> if (s = "I_")||(s = "U_")||(s = "n")||(s = "addr_mode") then ("",0,0) else (s, i1, i2)) lst
    | _ -> lst;;


(*translate variables in order to call the defined functions
 to get the required varialbe*)
let inst_param ls =
  match ls with
    | (("s" | "m" | "n" | "d" | "dHi" | "dLo"), i, _) ->
	Printf.sprintf "(regnum_from_bit %d w)" i
    | ("shifter_operand", _, _) ->
	"(decode_shifter_operand w I x)"
    | ("cond", _, _) ->	"op" (*REMOVE:"(condition w)"*)
    | (s, p, l) -> 
	if l > 1 then 
	  Printf.sprintf "w[%d#%d]" (p+l-1) p
	else
	  Printf.sprintf "%s" s
;;

(*keep only one of the same elements in a range*)
(*rerange the data type of instruction parameters with name, position and length*)
let param_m ar =
  let res = Array.create (Array.length ar) ("", 0, 0) in
    for i = 0 to (Array.length ar -1) do
      match ar.(i) with
	| Range (s, len, _) ->
	    if s.[0] = 'R' then
	      res.(i) <- ((String.sub s 1 (String.length s -1)), i, len)
	    else
	      if s = "ImmedL" then
		res.(i) <- ("immedL", i, len)
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

(*get the final well typed parameters list*)
let params f (lh, ls) =
  let dname = name (name_lst (lh,ls)) in
  let n = name_lst (lh, ls) in
  let aux b =
    let lst =
	(List.filter ((<>) "")
	      (List.map inst_param
		    (remove_var_cond dname
		       (remove_vars n
			  (add_mode_var dname
			     (List.sort (fun (s1, _, _) (s2, _, _) -> 
					   Pervasives.compare s1 s2)
				(Array.to_list (param_m ls))))))))
    in
      (list " " f) b lst
  in aux;;

(*****************************************************************************)
(** should be one/zero test *)
(*****************************************************************************)

(*return SBO with its position*)
let sbo_tst ls =
  match ls with
    | (Shouldbe true, i) -> Printf.sprintf "SBO%d" i
    | ((Nothing | Value _ | Param1 _ | Param1s _ | Range _ | Shouldbe false), _)
      -> "";;

(*return SBZ with its position*)
let sbz_tst ls =
  match ls with
    | (Shouldbe false, i) -> Printf.sprintf "SBZ%d" i
    | ((Nothing | Value _ | Param1 _ | Param1s _ | Range _ | Shouldbe true), _)
      -> "";;

(*insert a test of should be one/zero in decoding*)
let shouldbe_test (lh, ls) =
  (*let lst = Array.to_list ls in
  let ps = Array.to_list (pos_info ls) in
  let sbo = List.filter ((<>) "") (List.map sbo_tst ps) in
  let sbz = List.filter ((<>) "") (List.map sbz_tst ps) in*)
  let aux b =
    (*if ((List.mem (Shouldbe true) lst) && (not (List.mem (Shouldbe false) lst))) then
      bprintf b "if (%a) then\n      DecInst (%s %t)\n      else DecUnpredictable"
	(list "&& " string) sbo (id_inst (lh,ls)) (params string (lh, ls))
    else 
      if (List.mem (Shouldbe false) lst && (not (List.mem (Shouldbe true) lst))) then
	bprintf b "if (not (%a)) then \n      DecInst (%s %t)\n      else DecUnpredictable"
	  (list "&& " string) sbz (id_inst (lh,ls)) (params string (lh, ls))
      else 
	if (List.mem (Shouldbe false) lst && (List.mem (Shouldbe true) lst)) then
	  bprintf b "if ((%a) && (not (%a))) then \n      DecInst (%s %t)\n      else DecUnpredictable"
	 (list "&& " string) sbo (list "&& " string) sbz (id_inst (lh,ls)) (params string (lh, ls))
	else*)
	  bprintf b "%s %t" (id_inst (lh,ls)) (params string (lh, ls))
  in aux;;

(*****************************************************************************)
(** call addressing mode function in instruction*)
(*****************************************************************************)

(*call the decode mode function according to the addressing mode*)
let mode_tst (lh, ls) =
  let aux b =
  let lst = Array.to_list (param_m ls) in
  let md = mode_var (name_lst (lh, ls)) lst in
  match md with
    | (1|2|3|4|5 as i) -> bprintf b "decode_cond_mode decode_addr_mode%d w (fun i op => %t)" i (shouldbe_test (lh, ls))
    | _ -> bprintf b "decode_cond w (fun op => %t)" (shouldbe_test (lh, ls))
  in aux;;

(*****************************************************************************)
(** constructor for instructions and addressing mode *)
(*****************************************************************************)

let dec_inst b (lh, ls) =
  let dbits = pos_info ls in
    let md = add_mode (name_lst (lh,ls)) in
      match md with
	| Inst -> 
	    bprintf b "    %a\n    | %t =>\n      %t\n"
	      comment lh (bits dec dbits) (mode_tst (lh, ls))
	| Encoding -> ()
	| Addr_mode i ->
	    (*FIXME*)
	    if i = 1 || (i = 2 && false) || (i = 3 && false) then
	      bprintf b "    %a\n    | %t =>\n      DecInst (%s %t)\n"
		comment lh (bits dec dbits)
		(id (lh, ls)) (params string (lh, ls))
	    else
	      bprintf b "    %a\n    | %t =>\n      decode_cond w (fun op => %s %t)\n"
		comment lh (bits dec dbits)
		(id (lh, ls)) (params string (lh, ls))
;;

(*****************************************************************************)
(** ordering *)
(*****************************************************************************)

(*ordering the instruction and addressing mode for decoder in order to avoid the
 matching reduntancy*)
let order_ad p =
  match num p with
    | 13 -> 0
    | _ -> 1;;

let order_inst p =
  match num p with
    | 45 -> -6
    | (8|59|67) -> -5
    | (7|16|90|126) -> -4
    | (124|125) -> -3
    | (121|122|123|130|131|132|133|134|135|148) -> -2
    | 145 -> -1
    | 115 -> 0
    | (112|113) -> 1
    | (110|114) -> 2
    | (71|72|73) -> 3
    | 70 -> 4
    | (69|68) -> 5
    | (56|57|58) -> 6
    | (34|37|40|62|63) -> 7
    | (46|47|48|49|50|53|54|55|64|85|84) -> 8
    | (74|76|77|82|83|87|89|91|92|93|94|95|103|108|109|111|146) -> 9
    | (143|147) -> 10
    | 144 -> 11
    | (118|119|120) ->12
    | (25|31|105) -> 14
    | (35|106|116|117) -> 15
    | (99|100) -> 16
    | (23|24|41|42|65) -> 17
    | (60|61|18) -> 18
    | (2|3|4|6|14|15) -> 19
    | _ -> 13;;

(*separate the instruction and address mode data*)
let is_inst l =
  if ((add_mode (name_lst l)) = Inst) then true else false;;

let is_addr_mode i l =
  if ((add_mode (name_lst l)) = Addr_mode i) then true else false;;

(*****************************************************************************)
(** main decoder functions: addressing mode decoder and instruction decoder *)
(*****************************************************************************)

let decode b ps =
(*print the import require and notations*)
  string b "Require Import Bitvec List Util Functions Config Arm State Semantics ZArith arm6inst Simul String.\n\nOpen Scope string_scope.\n\nLocal Notation \"0\" := false.\nLocal Notation \"1\" := true.\nLocal Infix \"\'\" := cons (at level 60, right associativity).";
(*print the decoder of address mode 1*)
  string b "\n\nDefinition decode_addr_mode1 (w : word) : decoder_result mode1 :=\n match bools_of_word w with\n";
  (list "" dec_inst) b (List.sort (fun a b -> order_ad a - order_ad b) (List.filter (is_addr_mode 1) ps));
  string b "    | _ => DecError mode1 \"not a addressing mode 1\"\n  end.";
(*print the decoder of addrss mode 2 - 5*)
  for i = 2 to 5 do
    bprintf b "\n\nDefinition decode_addr_mode%d (w : word) : decoder_result mode%d:=\n match bools_of_word w with\n" i i;
  (list "" dec_inst) b (List.filter (is_addr_mode i) ps);
  bprintf b "    | _ => DecError mode%d \"not a addressing mode %d\"\n  end." i i
  done;
(*print the instruction decoder*)
  bprintf b "\n\nDefinition decode (w : word) : decoder_result inst :=\n  match bools_of_word w with\n";
  (list "" dec_inst) b (List.sort (fun a b -> order_inst a - order_inst b) (List.filter (is_inst) ps));
  bprintf b "    | _ => DecUndefined inst\n  end."
;;
