(**
SimSoC-Cert, a library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

All the patch functions used by simlight2
*)

open Ast;;
open Util;;
open Flatten;;

(* After instantiation of the addressing mode, the condition may be
 * evaluated many times. Moreover, it is always better to test it at the
 * beginning
 * - The function below remove the condition tests that are inside.
 * - Another function add one condition check at the beginning. *)
let rec remove_cond_passed i = 
  let rec flatten = function
    | Block is :: tl -> is @ flatten tl
    | i :: tl -> i :: flatten tl
    | [] -> []
  in match i with
    | Block is -> Block (flatten (List.map remove_cond_passed is))
    | If (Fun ("ConditionPassed", [Var "cond"]), i, None) -> i
    | If (BinOp (Fun ("ConditionPassed", [Var "cond"]), "and", e), i, None) ->
        If (e, i, None)
    | If (c, i, None) -> If (c, remove_cond_passed i, None)
    | If (c, i, Some i') -> If (c, remove_cond_passed i, Some (remove_cond_passed i'))
    | _ -> i;;

(* Some Load-Store addressing modes modify the address register (Rn)
 * This modification should not happen before the last memory access
 * because a failed memory access cancels this register writeback. *)
let postpone_writeback (pcs: prog list) =
  let init_new =  Block [
    Affect (Var "new_Rn", Hex "0xBAD"); (* avoid g++ warnings *)
    Affect (Var "old_mode", Fun ("get_current_mode", []))] in
  let prog p =
    let rec inst = function
      | Block is -> Block (List.map inst is)
      | Affect (Reg (Var "n", None), e) -> Affect (Var "new_Rn", e)
      | If (c, i, None) -> If (c, inst i, None)
      | If (c, i, Some i') -> If (c, inst i, Some (inst i'))
      | While (e, i) -> While (e, inst i)
      | For (s1, s2, s3, i) -> For (s1, s2, s3, inst i)
      | Case (e, sis) -> Case (e, List.map (fun (s,i) -> (s, inst i)) sis)
      | i -> i
    in match p.pkind with
      | InstARM | InstThumb -> p
      | Mode _ ->
          let i = remove_cond_passed p.pinst in
          let i' = inst i in 
            if i = i' then {p with pinst = i}
            else {p with pinst = merge_inst init_new i'}
  in List.map prog pcs;;

(* insert_writeback is given latter, after the definition of xprog *)

(* address_of_next_instruction() cannot be ued because it reads the
 * current value of the PC instead of the original one.
 * See for example BL, BLX (1) in thumb instruction set *)
let patch_addr_of_next_instr (p: fprog) =
  let o = Fun ("address_of_next_instruction", [])
  and n = Var "addr_of_next_instr" in
    try 
      let i = replace_exp o n p.finst in
      let size = if p.fkind = ARM then "4" else "2" in
      let a = Affect (Var "addr_of_next_instr",
                      BinOp (Reg (Num "15", None), "-", Num size))
      in {p with finst = merge_inst a i}
    with Not_found -> p;;

(* coprocessor statments require additional arguments *)
let patch_coproc (p: fprog) =
  if p.finstr = "STC" || p.finstr = "LDC" (* TODO *)
  then {p with finst = Proc ("exec_undefined_instruction", [])}
  else
    let args = function
      | "MCR" | "MRC" -> [Var "opcode_1"; Var "opcode_2"; Var "CRn"; Var "CRm"]
      | _ -> [] in
    let rec inst = function
      | Block is -> Block (List.map inst is)
      | If (e, i1, Some i2) -> If (e, inst i1, Some (inst i2))
      | If (e, i, None) -> If (e, inst i, None)
      | While (e, i) -> While (e, inst i)
      | For (s1, s2, s3, i) -> For (s1, s2, s3, inst i)
      | Case (e, sis) ->
          Case (e, List.map (fun (s, i) -> (s, inst i)) sis)
      | Coproc (e, s, es) -> Coproc (e, s, args p.finstr @ es)
      | Affect (d, Coproc_exp (e, s, es)) ->
          Affect (d, Coproc_exp (e, s, args p.finstr @ es))
      | i -> i
    in {p with finst = inst p.finst};; 

(* test the CP15 U bit after the alignment, because the unaligned case is rare *)
let swap_u_test (p: fprog) =
  let aux = function
    | BinOp (BinOp (Fun ("CP15_reg1_Ubit", []), "==", Num "0") as u, "and", e) ->
       BinOp (e, "and", u)
    | x -> x
  in {p with finst = ast_exp_map aux p.finst};;

(** Optimize the sub-expressions that can be computed at decode-store time. *)

let computed_params (p: fprog) (ps: (string*string) list) =
  try
  if List.mem_assoc "register_list" ps then
    (* we compute "Number_Of_Set_Bits_In(register_list) * 4" *)
    let o = BinOp (Fun ("Number_Of_Set_Bits_In", [Var "register_list"]),
                   "*", Num "4")
    and n = Var "nb_reg_x4" in
    let p' = {p with finst = replace_exp o n p.finst} in
      if p.finstr="LDM2" || p.finstr="STM2" then (
        (* we know that W is 0 *)
        assert (List.mem_assoc "W" ps);
        let p'' = {p with finst = replace_exp (Var "W") (Num "0") p.finst}
        and remove (s,_) = s <> "W" in
          p'', List.filter remove ps, [("nb_reg_x4", "uint8_t")]
      ) else p', ps, [("nb_reg_x4", "uint8_t")]
  else if List.mem_assoc "signed_immed_24" ps then
    let se_lsl_2 = BinOp (Fun ("SignExtend_30", [Var "signed_immed_24"]),
                          "<<", Num "2") in
      if List.mem_assoc "H" ps then
        (* we compute "(SignExtend_30(signed_immed_24) << 2) + (H << 1)" *)
        let pc = Reg (Num "15", None) in
        let tmp = BinOp (pc, "+", se_lsl_2) in
        let o = BinOp (tmp, "+", BinOp (Var "H", "<<", Num "1"))
        and n = BinOp (pc, "+", Var "pc_offset_h") 
        and remove (s,_) = s <> "H" && s <> "signed_immed_24" in
        let p' = {p with finst = replace_exp o n p.finst} in
          p', List.filter remove ps, [("pc_offset_h", "uint32_t")]
      else
        (* we compute "(SignExtend_30(signed_immed_24) << 2)" *)
        let n = Var "pc_offset"
        and remove (s,_) = s <> "signed_immed_24" in
        let p' = {p with finst = replace_exp se_lsl_2 n p.finst} in
          p', List.filter remove ps, [("pc_offset", "uint32_t")]
  else if List.mem_assoc "rotate_imm" ps then (
    (* we compute immed_8 Rotate_Right (rotate_imm * 2) *)
    assert (List.mem_assoc "immed_8" ps);
    let tmp = BinOp (Var "rotate_imm", "*", Num "2") in
    let o = BinOp (Var "immed_8", "Rotate_Right", tmp)
    and n = Var "immed_rotated"
    and remove (s,_) =  s <> "immed_8" in
    let p' = {p with finst = replace_exp o n p.finst} in
      p', List.filter remove ps, [("immed_rotated", "uint32_t")])
  else if List.mem_assoc "offset_12" ps then (
    (* we pre-compute the sign, which is given by the U bit*)
    assert (List.mem_assoc "U" ps);
    let remove (s,_) = s <> "U" && s <> "offset_12" in
      (* there are two cases. The result is stored either in Rn or in address *)
    let u = BinOp (Var "U", "==", Num "1")
    and rn = Reg (Var "n", None) in
    let plus = BinOp (rn, "+", Var "offset_12")
    and minus = BinOp (rn, "-", Var "offset_12") in
    let o = If_exp (u, plus, minus)
    and n = BinOp (rn, "+", Var "signed_offset_12") in
      try
        (* Case 1: we search a conditional expression *)
        let inst = replace_exp o n p.finst in
        let p' = {p with finst = inst} in
          p', List.filter remove ps, [("signed_offset_12", "uint32_t")]
      with Not_found ->
        (* Case 2: we search a conditional instruction *)
        let o' = If (u, Affect (Var "new_Rn", plus),
                     Some (Affect (Var "new_Rn", minus)))
        and n' = Affect (Var "new_Rn", n) in
        let inst' = replace_inst o' n' p.finst in
        let p' = {p with finst = inst'} in
          p', List.filter remove ps, [("signed_offset_12", "uint32_t")])
  else p, ps, []
  with Not_found -> p, ps, [];;

let compute_param = function
  | "nb_reg_x4" -> "Number_Of_Set_Bits_In(register_list) * 4"
  | "pc_offset_h" -> "(SignExtend_30(signed_immed_24) << 2) + (H << 1)"
  | "pc_offset" -> "SignExtend_30(signed_immed_24) << 2"
  | "immed_rotated" -> "rotate_right(immed_8,rotate_imm*2)"
  | "signed_offset_12" -> "(U ? offset_12 : -offset_12)"
  | _ -> raise (Invalid_argument "compute_param");;

(** extended program type allowing to store extra information *)

type group = int * (string * string) list;; (* = id * parameters *)

type xprog = {
  xprog: fprog;
  xps: (string * string) list; (* parameters *)
  xls: (string * string) list; (* local variables *)
  xcs: (string * string) list; (* computed parameters *)
  xkps: (string * string) list; (* parameters without the ones replaced
                                 * by computed prameters *)
  xgid: int; (* id of the group *)
}

let union_id x = "g" ^ string_of_int x.xgid;;

let sizeof t = match t with
  | "uint8_t" | "bool" -> 1
  | "uint16_t" -> 2
  | "uint64_t" -> 8
  | _ -> 4;;

let xprogs_of ps =
  let groups: group list ref = ref [(0, [])] in
  let gid kps cs =
    let ps =
      (* fields are sorted according to their size, in order to minimize
       * padding bytes *)
      let cmp (_,t) (_,t') = compare (sizeof t) (sizeof t')
      in List.stable_sort cmp (kps @ cs)
    in
      try fst (List.find (fun (_, x) -> x = ps) !groups)
      with Not_found -> match !groups with
        | (n, _) :: _ -> groups := (n+1, ps) :: !groups; n+1
        | [] -> raise (Failure "error while computing group id")
  in let xprog_of p =
      let ps, ls = Gencxx.V.vars p.finst in
      let p', kps, cs = computed_params p ps in
      let p'' = {p' with finst = remove_cond_passed p'.finst} in
        {xprog = p''; xps = ps; xls = ls; xcs = cs; xkps = kps; xgid = gid kps cs}
  in List.rev (List.map xprog_of ps), !groups;;

(** specialization according to the condition field *)

let is_conditional (p: xprog) = List.mem_assoc "cond" p.xps;;

let has_writeback (p: xprog) =
  List.mem_assoc "new_Rn" p.xls &&
    p.xprog.finstr <> "LDM2" && p.xprog.finstr <> "STM2";;

(* Cf. postpone_writeback
 * We insert the writeback after the last memory access.
 * Inserting at the end would fail, because the processor mode 
 * may have changed. *)
let insert_writeback (xs: xprog list) =
  let wb x = 
    let aux = match x.xprog.finstr with
      | "LDM3" -> Proc ("set_reg_m", [Var "n"; Var "old_mode"; Var "new_Rn"])
      | "SRS" -> Proc ("set_reg_m", [Num "13"; Var "mode"; Var "new_Rn"])
      | _ -> Affect (Reg (Var "n", None), Var "new_Rn")
    in if List.mem_assoc "W" x.xkps
      then If (BinOp (Var "W", "==", Num "1"), aux, None)
      else aux
  in let prog x =
    if has_writeback x then
      let inst = function
        | Block is -> Block (is @ [wb x])
        | _ -> raise (Failure "insert_writeback")
      in {x with xprog = {x.xprog with finst = inst x.xprog.finst}}
    else x
  in List.map prog xs;;

(* for each instruction with a condition, we generate a variant without the condition *)
let no_cond_variants xs =
  let prog x =
    let p = x.xprog in
    let p' =
      {p with fid = p.fid^"_NC"; fref = p.fref^"--NC"; fname = p.fname^" (no cond)"}
    in {x with xprog = p'; xps = List.remove_assoc "cond" x.xps}
  in List.map prog (List.filter is_conditional xs);;
