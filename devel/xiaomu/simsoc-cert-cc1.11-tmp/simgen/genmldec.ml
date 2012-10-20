(**
SimSoC-Cert, a toolkit for generating certified processor simulators
See the COPYRIGHTS and LICENSE files.

Generator of the OCaml instruction decoder.
*)

open Ast;;
open Printf;;
open Util;;
open Codetype;;
open Dec;;
open Dec.Arm6;;
open Lightheadertype;;

(*****************************************************************************)
(** generate the comment above the pattern *)
(*****************************************************************************)

let comment b (lh: lightheader) =
  let lightheader b (p: lightheader) =
    match p with LH (is, s)
        -> bprintf b "%a - %s" (list_sep "." int) is s
  in
    bprintf b "(*%a*)" lightheader lh;;

(*****************************************************************************)
(** compute function names *)
(*****************************************************************************)

(* function used to generate the Coq function name for an addressing mode*)
let id_addr_mode (ps: maplist_element) =
  let rec concatenate = function
    | [] -> ""
    | [s] -> s
    | s :: ss -> s ^ "_" ^ concatenate ss
  in
    concatenate (name ps);;

(* function used to generate the Coq function name for an instruction*)
let id_inst (ps: maplist_element) =
  let rec concatenate = function
    | [] -> ""
    | [s] -> s
    | s :: ss -> s ^ concatenate ss
  in
    concatenate (name ps);;

(*****************************************************************************)
(** add addressing mode parameter to instructions *)
(*****************************************************************************)

(* return the addressing mode used by the instruction 'm' according to its name and parameters*)
(* m is the name of the instruction *)
(* The fisrt element of an lst element is a parameter name *)
let mode_of_inst (m: string list) (lst: (string*int*int) list) =
  let parameter_names = List.map (fun (s,_,_) -> s) lst in
  let inst_basename = List.hd m in
  let mode3 = ["LDRD";"LDRH";"LDRSB";"LDRSH";"STRD";"STRH"] in
  let mode4 = ["RFE";"SRS"] in
  let mode5 = ["LDC";"STC"] in
    if (List.mem "shifter_operand" parameter_names) then 1
    else if (List.mem "register_list" parameter_names) then 4
    else if (List.mem "addr_mode" parameter_names) then
      if (List.mem inst_basename mode3) then 3 else 2
    else if (List.mem inst_basename mode4) then 4
    else if (List.mem inst_basename mode5) then 5
    else 0;;

(* add address mode variable in the parameter list*)
(* 'n' is the name of an instruction, represented by a string list *)
let add_mode_param (md: kind) (n: string list) lst =
  match md with
    | DecInstARMCond | DecInstARMUncond ->
        if (mode_of_inst n lst != 0) then
          List.append [("add_mode", 0, 0)] lst
        else lst
    | DecInstThumb | DecMode _ | DecEncoding -> lst;;


(*****************************************************************************)
(** binary list *)
(*****************************************************************************)

(*add the position of element in the array*)
let pos_info (_, pc) =
  let ar = Array.create (Array.length pc) (Nothing, 0) in
    for i = 0 to Array.length pc - 1 do
      ar.(i) <- (pc.(i), i)
    done;
    ar;;

(*translate array content to binary and variable.
 * That is to say, we generate the "pattern"
(* The bits are separated by ' *)
 *)
let gen_pattern (lh ,ls) =
  let x = pos_info (lh, ls) in
  let dec ls =
    match ls with
      | (Value s, _) ->
          begin match s with
            | true -> "true"
            | false -> "false"
          end
      | (Shouldbe s, i) ->
          begin match s with
            | true -> "sBO"^(string_of_int i)
            | false -> "sBZ"^(string_of_int i)
          end
      | (Param1 c, _) -> Char.escaped (Char.lowercase c)^"_"
      | (Param1s s, _) -> s
      | (Range ("cond", _, _), _) -> ""
      | (Range _, _) -> "_"
      | (Nothing, _) -> ""
  in
  let aux b =
    let dec_lst l = List.filter ((<>)"") (List.map dec (List.rev l)) in
    match add_mode lh with
      | DecInstARMUncond -> 
          let lst = Array.to_list (Array.sub x 0 28) in
            (list_sep ", " string) b (dec_lst lst)
      | DecInstARMCond -> begin match name (lh ,ls) with
          | "BKPT" :: _ -> let lst = Array.to_list (Array.sub x 0 28) in
              (list_sep ", " string) b (dec_lst lst)
          | _ -> let lst = Array.to_list x in
              (list_sep ", " string) b (dec_lst lst)
        end
      | DecMode _ | DecInstThumb | DecEncoding ->
          let lst = Array.to_list x in
            (list_sep ", " string) b (dec_lst lst)
  in aux;;

(*****************************************************************************)
(** remove unused parameters from instructions and addressing mode cases *)
(*****************************************************************************)

(* Some parameters appears in the encoding but not in the AST.
 * We must remove them.
 *)

(*remove the unused one from the parameter list
 according to addressing mode 'i'*)
let not_param_add_mode i =
  match i with
    | 1 -> ["s_"; "cond"; "d"; "n"; "opcode"]
    | 2 -> ["b_"; "l_"; "d"; "h_"; "s_"]
    | 3 -> ["b_"; "l_"; "d"; "h_"; "s_"]
    | 4 -> ["l_"; "s_"; "CRd"; "n_"; "option"; "i"]
    | 5 -> ["l_"; "s_" ; "CRd"; "n_"; "option"]
    | _ -> [];;

let not_param_inst i =
  match i with
    | 1 -> ["shifter_operand"; "i_"]
    | 2 -> ["p_"; "u_"; "w_"; "addr_mode"; "i_"]
    | 3 -> ["i_"; "p_"; "w_"; "u_"; "n"; "addr_mode"]
    | 4 -> ["p_"; "u_"; "w_"; "n"; "mode"]
    | 5 -> ["offset_8"; "CRd"; "p_"; "u_"; "w_"; "n_"; "n"]
    | _ -> [];;

let is_not_param_add_mode i =
  fun (s, _, _) -> List.mem s (not_param_add_mode i);;

let is_not_param_inst i =
  fun (s, _, _) -> List.mem s (not_param_inst i);;

(* 'n' is the instruction or addressing mode case name *)
(* 'lst' is the list of parameters *)
(* This function returns a new parameter list without unused parameters *)
let remove_params (md: kind) n lst =
  (* We do that in two steps *)
  let remove_params_step1 lst =
    List.map (fun s -> if (
                match md with
                  | DecMode i -> is_not_param_add_mode i s
                  | DecInstARMCond | DecInstARMUncond ->
                      let im = mode_of_inst n lst in
                        is_not_param_inst im s
                  | DecInstThumb -> false (* TODO: Thumb mode *)
                  | DecEncoding -> false) then
                ("",0,0) else s) lst
  in
    (*remove variable in other cases*)
  let remove_params_step2 lst =
    match n with
      (* some addressing mode cases use 'cond' in the AST, and others does not *)
      | ("M2" ::_ :: "offset" :: _ |"M2" ::_ :: _ :: "offset" :: _ | "M3" :: _ :: "offset" :: _) ->
          List.map (fun (s, i1, i2) ->
                      if (s = "cond") then ("",0,0) else (s, i1, i2)) lst

      | ("MRC"|"MCR"|"MCRR"|"CDP"|"MRRC")::_ ->
          List.map (fun (s, i1, i2) ->
                      if (s = "opcode_1")||(s = "opcode_2")||(s ="CRd")||(s = "CRm")||(s = "CRn")||(s = "opcode") then ("",0,0) else (s, i1, i2)) lst

      | "M5" :: "Unindexed" :: _ ->
          List.map (fun (s, i1, i2) -> if (s = "u_") then ("",0,0) else (s, i1, i2)) lst

      | "SWI" :: _ -> List.map (fun (s, i1, i2) -> if (s = "immed_24") then ("",0,0) else (s, i1, i2)) lst

      | ("LDRB"|"LDRBT"|"STRB"|"LDR"|"STR"|"STRBT"|"LDRT"|"STRT") :: _ -> List.map (fun (s, i1, i2) -> if (s = "n") then ("",0,0) else (s, i1, i2)) lst
      (* PLD is a mode 2 instruction but the AST does not used the mode, so we remove 'add_mode' *)
      | ("PLD") :: _ -> List.map (fun (s, i1, i2) -> if (s = "add_mode")|| (s = "i_")||(s = "u_")||(s = "n")||(s = "addr_mode") then ("",0,0) else (s, i1, i2)) lst

      | _ -> lst
  in
    remove_params_step2 (remove_params_step1 lst);;

(* translate parameters in order to call the defined functions
 to get the required parameter *)
let inst_param ls =
  match ls with
    | (("s" | "m" | "n" | "d" | "dHi" | "dLo"), i, _) ->
        Printf.sprintf "(regnum_from_bit n%d w)" i
    | ("cond", _, _) -> "condition" (*REMOVE:"(condition w)"*)
    | (s, p, l) ->
        if l > 1 then
          Printf.sprintf "(bits n%d n%d w)" (p+l-1) p
        else
          Printf.sprintf "%s" s
;;

(* keep only one of the same elements in a range *)
(* rerange the data type of instruction parameters
  with name, position and length *)
let param_m (_, ls) =
  let res = Array.create (Array.length ls) ("", 0, 0) in
    for i = 0 to (Array.length ls -1) do
      match ls.(i) with
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
    for i = 0 to (Array.length ls -1) do
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

let to_lowercase (str, a, b) =
  if String.length str = 2 && String.get str 1 = '_' then
    ((Char.escaped (Char.lowercase (String.get str 0)))^"_",a,b)
  else (str, a, b)
;;

(* get the final well typed parameters list *)
let params f (lh, ls) =
  let dname = name (lh,ls) 
  and md = add_mode lh in
  let aux b =
    let lst =
      (List.filter ((<>) "")
         (List.map inst_param
               (remove_params md dname
                  (add_mode_param md dname
                     (List.map to_lowercase
                        (List.sort (fun (s1, _, _) (s2, _, _) ->
                                      Pervasives.compare s1 s2)
                           (Array.to_list (param_m (lh,ls)))))))))
    in
      if List.length lst > 1 then par (list_sep ", " f) b lst
      else (list_sep ", " f) b lst
  in aux;;

(*****************************************************************************)
(** should be one/zero test *)
(*****************************************************************************)

(* FIXME: Actually, the code in this section does nothing *)

(*return SBO with its position*)
let sbo_tst ls =
  match ls with
    | (Shouldbe true, i) -> Printf.sprintf "sBO%d" i
    | ((Nothing | Value _ | Param1 _ | Param1s _ | Range _ | Shouldbe false), _)
      -> "";;

(*return SBZ with its position*)
let sbz_tst ls =
  match ls with
    | (Shouldbe false, i) -> Printf.sprintf "sBZ%d" i
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
        (list_sep "&& " string) sbo (id_inst (lh,ls)) (params string (lh, ls))
    else
      if (List.mem (Shouldbe false) lst && (not (List.mem (Shouldbe true) lst))) then
        bprintf b "if (not (%a)) then \n      DecInst (%s %t)\n      else DecUnpredictable"
          (list_sep "&& " string) sbz (id_inst (lh,ls)) (params string (lh, ls))
      else
        if (List.mem (Shouldbe false) lst && (List.mem (Shouldbe true) lst)) then
          bprintf b "if ((%a) && (not (%a))) then \n      DecInst (%s %t)\n      else DecUnpredictable"
         (list_sep "&& " string) sbo (list_sep "&& " string) sbz (id_inst (lh,ls)) (params string (lh, ls))
        else*)
          bprintf b "%s %t" (id_inst (lh,ls)) (params string (lh, ls))
  in aux;;

(*****************************************************************************)
(** call addressing mode decoder in instruction*)
(*****************************************************************************)

(*call the decode mode function according to the addressing mode*)
let mode_tst (lh, ls) c =
  let aux b =
  let lst = Array.to_list (param_m (lh,ls)) in
  let md = mode_of_inst (name (lh, ls)) lst in
    if c then
      match md with
        | (1|2|3|4|5 as i) -> 
            bprintf b "decode_cond_mode decode_addr_mode%d w (fun add_mode condition -> %t)" 
              i (shouldbe_test (lh, ls))
        | _ -> bprintf b "decode_cond w (fun condition -> %t)" 
            (shouldbe_test (lh, ls))
    else
      match md with
        | (1|2|3|4|5 as i) -> 
            bprintf b "decode_mode decode_addr_mode%d w (fun add_mode -> %t)" 
              i (shouldbe_test (lh, ls))
        | _ -> bprintf b "DecInst (%t)" (shouldbe_test (lh, ls))
  in aux;;

(*****************************************************************************)
(** constructor for instructions and addressing mode *)
(*****************************************************************************)

let unconditional_instr =
 ["BLX1"; "CPS"; "PLD"; "RFE"; "SETEND"; "SRS"];;

let dec_inst b (lh, ls) =
  let md = add_mode lh in
    match md with
      | DecInstARMCond -> 
          bprintf b "    %a\n    | Coq_word28 (%t)->\n      %t\n"
            comment lh (gen_pattern (lh, ls)) (mode_tst (lh, ls) true)
      | DecInstARMUncond ->
          bprintf b "    %a\n    | Coq_word28 (%t)->\n      %t\n"
            comment lh (gen_pattern (lh, ls)) (mode_tst (lh, ls) false)
      | DecInstThumb -> () (* TODO: Thumb mode *)
      | DecEncoding -> ()
      | DecMode i ->
          (*FIXME*)
          if i = 1 || (i = 2 && false) || (i = 3 && false) then
            bprintf b "    %a\n    | Coq_word28 (%t) ->\n      DecInst (%s %t)\n"
              comment lh (gen_pattern (lh, ls))
              (id_addr_mode (lh, ls)) (params string (lh, ls))
          else
            bprintf b "    %a\n    | Coq_word28 (%t) ->\n      decode_cond w (fun condition -> %s %t)\n"
              comment lh (gen_pattern (lh ,ls))
              (id_addr_mode (lh, ls)) (params string (lh, ls))
;;

(*****************************************************************************)
(** ordering *)
(*****************************************************************************)

(*ordering the instruction and addressing mode for decoder in order to avoid the
 matching reduntancy*)

let sort_add_mode_cases i lst =
  match i with
    | 1 ->
        (* "Rotate Right with extend" (RRX) must be before "Rotate right by immediate" *)
        let order_ad p =
          match num p with
            | 13 -> 0
            | _ -> 1
        in
          List.sort (fun a b -> order_ad a - order_ad b) lst
    | _ -> lst;;

(* Numbers in pattern refers to instruction number, i.e.,
 * the subsection in which the instruction is defined *)
let order_inst p =
  match num p with
    | 45|8|59|67|16|90 -> -6 (* instruction without condition *)
    | 84|85|86|87|88|89|129|113|114|115|146|147|148 -> -1 (* instructions without accumulator *)
    | 9|10|11|13|39|40 -> 1 (* v5 instructions with SBO or SBZ can hide other v6 instructions *)
    | 25|105|31|101 -> 2 (* loadstore instructions with a 'T' *)
    | 28|102|104|30|26|29 -> 3
    | 38 -> 4
    | 19|20|21|22|96|97|98|35|106|116|117|99|100|23|24|41
        |42|65|18|60|61|2|3|4|6|14|15 -> 5 (* other instuctions with a mode*)
    | _ -> 0;;

(*separate the instruction and address mode data*)
let is_cond_inst (lh, _) = match add_mode lh with
  | DecInstARMCond | DecInstThumb -> true
  | DecEncoding | DecMode _ | DecInstARMUncond-> false;;

let is_uncond_inst (lh, _) = match add_mode lh with
  | DecInstARMUncond | DecInstThumb -> true
  | DecEncoding | DecMode _ | DecInstARMCond-> false;;

let is_addr_mode i (lh, _) = add_mode lh = DecMode i;;

(*****************************************************************************)
(** main decoder functions: addressing mode decoder and instruction decoder *)
(*****************************************************************************)

let decode b ps =
  (*print the import require*)
  string b "open Bitvec\nopen Integers\nopen Arm6_Message\nopen Simul\nopen Arm6_Inst\nopen Semantics\nopen Arm6_Functions.Semantics.Decoder\nopen Arm6_Functions.Semantics.S.Decoder_result\n";

  (*print the decoder of addressing modes 1 - 5*)
  for i = 1 to 5 do
    bprintf b "\n\nlet decode_addr_mode%d w =\n match w28_of_word w with\n" i;
    (list dec_inst) b (sort_add_mode_cases i (List.filter (is_addr_mode i) ps));
    bprintf b "    | _ -> DecError NotAnAddressingMode%d\n;;" i
  done;

  (*print the instruction decoder*)
  bprintf b "\n\nlet decode_unconditional w =\n  match w28_of_word w with\n";
  (list dec_inst) b (List.sort (fun a b -> order_inst a - order_inst b) (List.filter (is_uncond_inst) ps));
  bprintf b "    | _ -> DecUndefined_with_num n0\n;;";

  bprintf b "\n\nlet decode_conditional w =\n  match w28_of_word w with\n";
  (list dec_inst) b (List.sort (fun a b -> order_inst a - order_inst b) (List.filter (is_cond_inst) ps));
  bprintf b "    | _ -> DecUndefined_with_num n0\n;;";

  bprintf b "\n\nlet decode w =\n";
  bprintf b "  match w32_of_word w with\n";
  bprintf b "    | Coq_word32 (true, true, true, true, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _) ->\n";
  bprintf b "      decode_unconditional w\n";
  bprintf b "    | _ -> decode_conditional w\n";
  bprintf b "  ;;\n"
;;

