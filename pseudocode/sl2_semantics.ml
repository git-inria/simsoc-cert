(**
SimSoC-Cert, a library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Generate the semantics function used by simlight2
*)

(** Generate the code corresponding to an expression *)

open Ast;;
open Sl2_patch;;
open Flatten;;
open Util;;
open Printf;;

let implicit_arg = function
  | "ConditionPassed" -> "&proc->cpsr, "
  | "slv6_write_word_as_user" | "slv6_write_byte_as_user"
  | "slv6_write_word" | "slv6_write_half" | "slv6_write_byte" -> "proc->mmu_ptr, "
  | "CP15_reg1_EEbit" | "CP15_reg1_Ubit" | "CP15_reg1_Vbit" -> "proc->cp15_ptr"
  | "set_bit" | "set_field" -> "addr_of_"
  | "InAPrivilegedMode" | "CurrentModeHasSPSR" | "address_of_next_instruction"
  | "address_of_current_instruction" | "high_vectors_configured"
  | "get_current_mode" -> "proc"
  | "reg_m" | "set_reg_m" -> "proc, "
  | "exec_undefined_instruction" -> "proc, NULL"
  | _ -> "";;

let typeof x v =
  try List.assoc v x.xps
  with Not_found ->
    try List.assoc v x.xls
  with Not_found -> List.assoc v x.xcs;;

(* Load and Store instruction with a T suffix access the memory in special way *)
let lst (p: xprog) = match p.xprog.finstr with
  | "LDRT" | "LDRBT" | "STRT" | "STRBT" -> "_as_user"
  | _ -> "";;

let inst_size (p: xprog) =
  let pi = function
    | Affect (Ast.Range (CPSR, Flag ("T", _)), _)
    | Affect (Ast.Range (CPSR, Index (Num "5")), _) -> true
    | _ -> false
  in let exchange = inst_exists pi ffalse ffalse (* true if the instruction may switch ARM/Thumb mode *)
  in if exchange p.xprog.finst then "inst_size(proc)"
    else if is_thumb p.xprog then "2" else "4";;

(* true if <s> is encoded on 4 bits in the instruction p *)
let extended s p = is_arm p || (
  if s = "d" || s = "n" then List.mem ("H1", 7, 7) p.fparams
  else if s = "m" then List.mem ("H2", 6, 6) p.fparams
  else false);;

(* return true if the register <s> can be the PC in <p> *)
let pc_possible s (p: fprog) =
  not (List.mem (Validity.NotPC s) p.fvcs) && extended s p;;

let rec exp (p: xprog) b = function
  | Bin s -> string b (Gencxx.hex_of_bin s)
  | Hex s | Num s -> string b s
  | If_exp (e1, e2, e3) -> bprintf b "(%a? %a: %a)" (exp p) e1 (exp p) e2 (exp p) e3
  | BinOp (e1, ("Rotate_Right"|"Arithmetic_Shift_Right" as op), e2) ->
      (exp p) b (Fun (Gencxx.binop op, [e1; e2]))
  | BinOp (e, "<<", Num "32") ->
      bprintf b "(to_u64(%a) << 32)" (exp p) e
  | BinOp (e, ("<"|">=" as op), Num "0") ->
      bprintf b "(%a %s 0)" (exp p) (Gencxx.to_signed e) op
  | BinOp (Num n, "*", e) | BinOp (e, "*", Num n)->
      bprintf b "(%a * %s)" (exp p) e n
  | BinOp (e1, "*", e2) -> if p.xprog.fid.[0] = 'S'
    then bprintf b "(to_i64(%a) * to_i64(%a))" (exp p) e1 (exp p) e2
    else bprintf b "(to_u64(%a) * to_u64(%a))" (exp p) e1 (exp p) e2
  | BinOp (e1, op, e2) ->
      bprintf b "(%a %s %a)" (exp p) e1 (Gencxx.binop op) (exp p) e2

  (* try to find the right conversion operator *)
  | Fun ("to_signed", [Var v]) when typeof p v = "uint32_t" ->
      bprintf b "to_int32(%s)" v
  | Fun ("to_signed", [e]) -> bprintf b "to_int64(%a)" (exp p) e

  | Fun (f, es) -> bprintf b "%s(%s%a)"
      (Gencxx.func f) (implicit_arg f) (list ", " (exp p)) es
  | CPSR -> string b "StatusRegister_to_uint32(&proc->cpsr)"
  | SPSR None -> string b "StatusRegister_to_uint32(spsr(proc))"
  | SPSR (Some m) ->
      bprintf b "StatusRegister_to_uint32(spsr_m(proc,%s))" (Gencxx.mode m)
  | Reg (Var s, None) ->
      if List.mem s Gencxx.input_registers
      then bprintf b "old_R%s" s
      else bprintf b "reg(proc,%s)" s
  | Reg (e, None) -> bprintf b "reg(proc,%a)" (exp p) e
  | Reg (e, Some m) -> bprintf b "reg_m(proc,%a,%s)" (exp p) e (Gencxx.mode m)
  | Var s -> string b s
  | Memory (e, n) ->
      bprintf b "slv6_read_%s%s(proc->mmu_ptr,%a)" (Gencxx.access_type n) (lst p) (exp p) e
  | Ast.Range (CPSR, Flag (s,_)) -> bprintf b "proc->cpsr.%s_flag" s
  | Ast.Range (CPSR, Index (Num s)) -> bprintf b "proc->cpsr.%s" (Gencxx.cpsr_flag s)
  | Ast.Range (e1, Index e2) -> bprintf b "get_bit(%a,%a)" (exp p) e1 (exp p) e2
  | Ast.Range (e, Bits (n1, n2)) ->
      begin
        let signed = if p.xprog.fid.[0] = 'S' then "_signed" else if p.xprog.fid.[0] = 'Q' then "_signed" else "" in
          match n1, n2 with
            | "15", "0" -> bprintf b "get%s_half_0(%a)" signed (exp p) e
            | "31", "16" -> bprintf b "get%s_half_1(%a)" signed (exp p) e
            | "7", "0" -> bprintf b "get%s_byte_0(%a)" signed (exp p) e
            | "15", "8" -> bprintf b "get%s_byte_1(%a)" signed (exp p) e
            | "23", "16" -> bprintf b "get%s_byte_2(%a)" signed (exp p) e
            | "31", "24" -> bprintf b "get%s_byte_3(%a)" signed (exp p) e
            | _ -> bprintf b "get_bits(%a,%s,%s)" (exp p) e n1 n2
      end
  | _ -> string b "TODO(\"exp\")";;

(** Generate the body of an instruction function *)

let rec inst p k b = function
  | Block _ | For _ | While _ | If _ | Case _ as i ->
      bprintf b "%a%a" indent k (inst_aux p k) i
  | i -> bprintf b "%a%a;" indent k (inst_aux p k) i

and inst_aux p k b = function
  | Unpredictable -> bprintf b "unpredictable(\"%s\")" p.xprog.fid
  | Coproc (e, s, es) ->
      bprintf b "if (!slv6_%s_%s(proc,%a)) return"
        p.xprog.finstr s (list "," (exp p)) (e::es)
  | Affect (Var d, Coproc_exp (e, s, es)) ->
      bprintf b "if (!slv6_%s_%s(proc,&%s,%a)) return"
        p.xprog.finstr s d (list "," (exp p)) (e::es)
  | Affect (Reg (r, None), Coproc_exp (e, s, es)) ->
      bprintf b "if (!slv6_%s_%s(proc,addr_of_reg(proc,%a),%a)) return"
        p.xprog.finstr s (exp p) r (list "," (exp p)) (e::es)
  | Affect (dst, src) -> affect p k b dst src
  | Proc ("ClearExclusiveByAddress" as f, es) ->
      bprintf b "%s%d(%s%a)"
        f (List.length es) (implicit_arg f) (list ", " (exp p)) es
  | Proc (f, es) ->
      bprintf b "%s(%s%a)" f (implicit_arg f) (list ", " (exp p)) es
  | Assert e -> bprintf b "assert(%a)" (exp p) e

  | Block [] -> ()
  | Block (Block _ | For _ | While _ | If _ | Case _ as i :: is) ->
      bprintf b "%a\n%a" (inst_aux p k) i (list "\n" (inst p k)) is
  | Block (i :: is) ->
      bprintf b "%a;\n%a" (inst_aux p k) i (list "\n" (inst p k)) is

  | While (e, i) -> bprintf b "while (%a)\n%a" (exp p) e (inst p (k+2)) i

  | For (counter, min, max, i) ->
      bprintf b "size_t %s; for (%s = %a; %s<=%a; ++%s) {\n%a\n}"
        counter counter Gencxx.num min counter Gencxx.num max counter (inst p (k+2)) i

  | Case (e, s) ->
      bprintf b "switch (%a) {\n%a%a  default: abort();\n  }"
        (exp p) e (list "" (case_aux p k)) s indent k

  (* the condition has already been checked, or has been removed *)
  | If (Fun ("ConditionPassed", [Var "cond"]), _, None) ->
      raise (Failure "Unexpected condition check")

  | If (e, (Block _|If _ as i), None) ->
      bprintf b "if (%a) {\n%a\n%a}" (exp p) e (inst p (k+2)) i indent k
  | If (e, i, None) -> bprintf b "if (%a)\n%a" (exp p) e (inst p (k+2)) i

  | If (e, (Block _|If _ as i1), Some (Block _|If _ as i2)) ->
      bprintf b "if (%a) {\n%a\n%a} else {\n%a\n%a}"
	(exp p) e (inst p (k+2)) i1 indent k (inst p (k+2)) i2 indent k
  | If (e, (Block _|If _ as i1), Some i2) ->
      bprintf b "if (%a) {\n%a\n%a} else\n%a"
	(exp p) e (inst p (k+2)) i1 indent k (inst p (k+2)) i2
  | If (e, i1, Some (Block _|If _ as i2)) ->
      bprintf b "if (%a)\n%a\n%aelse {\n%a\n%a}"
	(exp p) e (inst p (k+2)) i1 indent k (inst p (k+2)) i2 indent k
  | If (e, i1, Some i2) ->
      bprintf b "if (%a)\n%a\n%aelse\n%a"
	(exp p) e (inst p (k+2)) i1 indent k (inst p (k+2)) i2

and case_aux p k b (n, i) =
  bprintf b "%acase %s:\n%a\n%abreak;\n"
    indent k (Gencxx.hex_of_bin n) (inst p (k+2)) i indent (k+2)

and affect (p: xprog) k b dst src =
  if src = Unpredictable_exp then bprintf b "unpredictable(\"%s\")" p.xprog.fid
  else match dst with
    | Reg (Var s, None) when s<>"i" ->
        if pc_possible s p.xprog
        then bprintf b "set_reg_or_pc_ws(proc,%s,%a,%s)" s (exp p) src (inst_size p)
        else bprintf b "set_reg(proc,%s,%a)" s (exp p) src
    | Reg (Num "15", None) -> bprintf b "set_pc_raw_ws(proc,%a,%s)" (exp p) src (inst_size p)
    | Reg (e, None) -> bprintf b "set_reg(proc,%a,%a)" (exp p) e (exp p) src
    | Reg (e, Some m) ->
	bprintf b "set_reg_m(proc,%a,%s,%a)" (exp p) e (Gencxx.mode m) (exp p) src
    | CPSR -> (
        match src with
          | SPSR None -> bprintf b "set_cpsr_sr(proc, *spsr(proc))"
          | SPSR (Some m) ->
              bprintf b "set_cpsr_sr(proc, *spsr_m(proc,%s))" (Gencxx.mode m)
          | _ -> bprintf b "set_cpsr_bin(proc, %a)" (exp p) src)
    | SPSR None -> (
        match src with
          | CPSR -> bprintf b "*spsr(proc) = proc->cpsr"
          | _ -> bprintf b "set_StatusRegister(spsr(proc),%a)" (exp p) src)
    | SPSR (Some m) -> (
        match src with
          | CPSR -> bprintf b "*spsr_m(proc,%s) = proc->cpsr" (Gencxx.mode m)
          | _ ->
              bprintf b "set_StatusRegister(spsr_m(proc,%s),%a)"
                (Gencxx.mode m) (exp p) src)
    | Var v -> bprintf b "%a = %a" (exp p) (Var v) (exp p) src
    | Ast.Range (CPSR, Flag (s,_)) ->
        bprintf b "proc->cpsr.%s_flag = %a" s (exp p) src
    | Ast.Range (CPSR, Index (Num ("6"|"7"|"8" as n))) ->
        bprintf b "set_cpsr_%s(proc,%a)" (Gencxx.cpsr_flag n) (exp p) src
    | Ast.Range (CPSR, Index (Num n)) ->
        bprintf b "proc->cpsr.%s = %a" (Gencxx.cpsr_flag n) (exp p) src
    | Ast.Range (CPSR, Bits ("19", "18")) ->
        bprintf b "set_GE_32(&proc->cpsr,%a)" (exp p) src
    | Ast.Range (CPSR, Bits ("17", "16")) ->
        bprintf b "set_GE_10(&proc->cpsr,%a)" (exp p) src
    | Ast.Range (CPSR, Bits ("4", "0")) ->
        bprintf b "set_cpsr_mode(proc, %a)" (exp p) src
    | Ast.Range (e1, Bits (n1, n2)) ->
        inst_aux p k b (Proc ("set_field", [e1; Num n1; Num n2; src]))
    | Memory (addr, n) ->
        inst_aux p k b (Proc ("slv6_write_" ^ Gencxx.access_type n ^ lst p, [addr; src]))
    | Ast.Range (e, Index n) -> inst_aux p k b (Proc ("set_bit", [e; n; src]))
    | _ -> string b "TODO(\"affect\")";;

(* display a comment with the reference and the full instruction name *)
let comment b x =
  bprintf b "/* %s\n * %s */\n" x.xprog.fref x.xprog.fname;;

(* check the instruction condition *)
let check_cond b p =
  if is_conditional p
  then bprintf b "  if (!ConditionPassed(&proc->cpsr, cond)) return;\n";;

(* Defintion of the functions. This should be printed in a source file (.c) *)
(* Version 1: The list of arguments is expanded *)
let prog_expanded b (p: xprog) =
  let ss = List.fold_left (fun l (s, _) -> s::l) [] p.xps in
  let inregs = List.filter (fun x -> List.mem x Gencxx.input_registers) ss in
    bprintf b "%avoid slv6_X_%s(struct SLv6_Processor *proc%a)\n{\n%a%a%a%a\n}\n"
      comment p
      p.xprog.fid
      (list "" Gencxx.prog_arg) p.xips
      check_cond p 
      (list "" Gencxx.inreg_load) inregs
      (list "" Gencxx.local_decl) p.xls
      (inst p 2) p.xprog.finst;;

(* Version 2: The arguments are passed in a struct *)
let prog_grouped b (p: xprog) =
  let ss = List.fold_left (fun l (s, _) -> s::l) [] p.xps in
  let inregs = List.filter (fun x -> List.mem x Gencxx.input_registers) ss in
    bprintf b
      "%avoid slv6_G_%s(struct SLv6_Processor *proc, struct SLv6_Instruction *instr) {\n"
      comment p p.xprog.fid;
    let expand b (n, t) =
      bprintf b "  const %s %s = instr->args.%s.%s;\n" t n (union_id p) n
    in
      bprintf b "%a%a%a%a%a\n}\n"
        (list "" expand) p.xips
        check_cond p
        (list "" Gencxx.inreg_load) inregs
        (list "" Gencxx.local_decl) p.xls
        (inst p 2) p.xprog.finst;;

(* Declaration of the functions. This may be printed in a header file (.h) *)
(* Version 1: The list of arguemetns is expanded *)
let decl_expanded b x =
  bprintf b "%aEXTERN_C void slv6_X_%s(struct SLv6_Processor*%a);\n"
    comment x x.xprog.fid (list "" Gencxx.prog_arg) x.xips;;

(* Version 2: The arguments are passed in a struct *)
let decl_grouped b x =
  let attr =
    if is_cold x then " SLV6_COLD"
    else if is_hot x then " SLV6_HOT"
    else ""
  in
    bprintf b "%a/* weight = %s */\n" comment x
      (match x.xw with Some n -> string_of_int n | None -> "?");
    bprintf b "extern void slv6_G_%s" x.xprog.fid;
    bprintf b "(struct SLv6_Processor*, struct SLv6_Instruction*)%s;\n" attr;;

(** Generation of all the semantics functions *)

(* Parameters:
 * - bn: file basename
 * - xs: the instructions
 * - v: a string, either "grouped" or "expanded"
 * - decl: a function, either decl_grouped or decl_expanded
 * - prog: a function, either prog_grouped or prog_expanded
 *)
let semantics_functions bn (xs: xprog list) (v: string) decl prog =
  let bh = Buffer.create 10000
  and hot_bc = Buffer.create 10000 and cold_bc = Buffer.create 10000 in
    (* header file *)
    bprintf bh "#ifndef SLV6_ISS_%s_H\n#define SLV6_ISS_%s_H\n\n" v v;
    bprintf bh "#include \"common.h\"\n";
    bprintf bh "#include \"slv6_mode.h\"\n";
    bprintf bh "#include \"slv6_condition.h\"\n";
    bprintf bh "\nBEGIN_SIMSOC_NAMESPACE\n";
    bprintf bh "\nstruct SLv6_Processor;\n";
    bprintf bh "struct SLv6_Instruction;\n";
    bprintf bh "\n%a" (list "\n" decl) xs;
    bprintf bh "\nEND_SIMSOC_NAMESPACE\n";
    bprintf bh "\n#endif /* SLV6_ISS_%s_H */\n" v;
    (* source files *)
    let hot_xs, cold_xs = List.partition is_hot xs in
      bprintf cold_bc "#include \"%s_c_prelude.h\"\n" bn;
      bprintf cold_bc "\n%a" (list "\n" prog) cold_xs;
      bprintf cold_bc "\nEND_SIMSOC_NAMESPACE\n";
      bprintf  hot_bc "#include \"%s_c_prelude.h\"\n" bn;
      bprintf  hot_bc "\n%a" (list "\n" prog) hot_xs;
      bprintf  hot_bc "\nEND_SIMSOC_NAMESPACE\n";
      let outh = open_out (bn^"_"^v^".h")
      and cold_outc = open_out (bn^"_"^v^".cold.c")
      and  hot_outc = open_out (bn^"_"^v^".hot.c") in
        Buffer.output_buffer outh bh; close_out outh;
        Buffer.output_buffer cold_outc cold_bc; close_out cold_outc;
        Buffer.output_buffer  hot_outc  hot_bc; close_out  hot_outc;;
