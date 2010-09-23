(**
SimSoC-Cert, a library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Generate additional C/C++ code for implementing dynamic translation in Simlight.
*)

open Ast;;
open Printf;;
open Util;;
open Dec;;
open Codetype;;
open Flatten;;

(** extended program type allowing to store extra information *)
type xprog = {
  xprog: fprog;
  xgs: (string * string) list; (* "global" variables *)
  xls: (string * string) list; (* local variables *)
  xbaseid: string; (* id without "_NC" *)
}

let xprog_of p =
  let gs, ls = Gencxx.V.vars p.finst in
    {xprog = p; xgs = gs; xls = ls; xbaseid = p.fid};;

(** specialization according to the condition field *)

let is_conditional p = List.mem_assoc "cond" p.xgs;;

let no_cond_variant x =
  let p = x.xprog in
  let p' =
    {p with fid = p.fid^"_NC"; fref = p.fref^"--NC"; fname = p.fname^" (no cond)"}
  in {x with xprog = p'; xgs = List.remove_assoc "cond" x.xgs};;

let no_cond_variants xs =
  List.map no_cond_variant (List.filter is_conditional xs);;

(** Generate the code corresponding to an expression *)

let typeof x v =
  try List.assoc v x.xgs
  with Not_found -> List.assoc v x.xls;;

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
      (Gencxx.func f) (Gencxx.implicit_arg f) (list ", " (exp p)) es
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
      bprintf b "read_%s(proc->mmu_ptr,%a)" (Gencxx.access_type n) (exp p) e
  | Ast.Range (CPSR, Flag (s,_)) -> bprintf b "proc->cpsr.%s_flag" s
  | Ast.Range (CPSR, Index (Num s)) -> bprintf b "proc->cpsr.%s" (Gencxx.cpsr_flag s)
  | Ast.Range (e1, Index e2) -> bprintf b "get_bit(%a,%a)" (exp p) e1 (exp p) e2
  | Ast.Range (e, Bits (n1, n2)) ->
      begin match n1, n2 with
        | "15", "0" -> bprintf b "get_half_0(%a)" (exp p) e
        | "31", "16" -> bprintf b "get_half_1(%a)" (exp p) e
        | "7", "0" -> bprintf b "get_byte_0(%a)" (exp p) e
        | "15", "8" -> bprintf b "get_byte_1(%a)" (exp p) e
        | "23", "16" -> bprintf b "get_byte_2(%a)" (exp p) e
        | "31", "24" -> bprintf b "get_byte_3(%a)" (exp p) e
        | _ -> bprintf b "get_bits(%a,%s,%s)" (exp p) e n1 n2
      end
  | Coproc_exp (e, f, es) ->
      bprintf b "%s(proc,%a)" (Gencxx.func f) (list "," (exp p)) (e::es)
  | _ -> string b "TODO(\"exp\")";;

(** Generate the body of an instruction function *)

let rec inst p k b = function
  | Block _ | For _ | While _ | If _ | Case _ as i ->
      bprintf b "%a%a" indent k (inst_aux p k) i
  | i -> bprintf b "%a%a;" indent k (inst_aux p k) i

and inst_aux p k b = function
  | Unpredictable -> string b "unpredictable()"
  | Affect (dst, src) -> affect p k b dst src
  | Proc (f, es) ->
      bprintf b "%s(%s%a)" f (Gencxx.implicit_arg f) (list ", " (exp p)) es
  | Assert e -> bprintf b "assert(%a)" (exp p) e
  | Coproc (e, f, es) ->
      bprintf b "%s(proc,%a)" (Gencxx.func f) (list "," (exp p)) (e::es)

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
  | If (Fun ("ConditionPassed", [Var "cond"]), i, None) -> inst p k b i

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
  if src = Unpredictable_exp then string b "unpredictable()"
  else match dst with
    | Reg (Var s, None) when s<>"i" ->
        if List.mem (Validity.NotPC s) p.xprog.fvcs
        then bprintf b "set_reg(proc,%s,%a)" s (exp p) src
        else bprintf b "set_reg_or_pc(proc,%s,%a)" s (exp p) src
    | Reg (Num "15", None) -> bprintf b "set_pc_raw(proc,%a)" (exp p) src
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
        inst_aux p k b (Proc ("write_" ^ Gencxx.access_type n, [addr; src]))
    | Ast.Range (e, Index n) -> inst_aux p k b (Proc ("set_bit", [e; n; src]))
    | _ -> string b "TODO(\"affect\")";;

(* display a comment with the reference and the full instruction name *)
let comment b p = bprintf b "/* %s\n * %s */\n" p.xprog.fref p.xprog.fname;;

(* check the instruction condition *)
let check_cond b p =
  if is_conditional p
  then bprintf b "  if (!ConditionPassed(&proc->cpsr, cond)) return;\n";;

(* Defintion of the functions. This should be printed in a source file (.c) *)
(* Version 1: The list of arguemetns is expanded *)
let prog_expanded b (p: xprog) =
  let ss = List.fold_left (fun l (s, _) -> s::l) [] p.xgs in
  let inregs = List.filter (fun x -> List.mem x Gencxx.input_registers) ss in
    bprintf b "%avoid slv6_X_%s(struct SLv6_Processor *proc%a)\n{\n%a%a%a%a\n}\n"
      comment p
      p.xprog.fid
      (list "" Gencxx.prog_arg) p.xgs
      check_cond p
      (list "" Gencxx.inreg_load) inregs
      (list "" Gencxx.local_decl) p.xls
      (inst p 2) p.xprog.finst;;

(* Version 2: The arguments are passed in a struct *)
let prog_grouped b (p: xprog) =
  let ss = List.fold_left (fun l (s, _) -> s::l) [] p.xgs in
  let inregs = List.filter (fun x -> List.mem x Gencxx.input_registers) ss in
    bprintf b
      "%avoid slv6_G_%s(struct SLv6_Processor *proc, struct SLv6_Instruction *instr) {\n"
      comment p p.xprog.fid;
    let expand b (n, t) =
      bprintf b "  const %s %s = instr->args.%s.%s;\n" t n p.xbaseid n
    in
      bprintf b "%a%a%a%a%a\n}\n"
        (list "" expand) p.xgs
        check_cond p
        (list "" Gencxx.inreg_load) inregs
        (list "" Gencxx.local_decl) p.xls
        (inst p 2) p.xprog.finst;;

(* Declaration of the functions. This may be printed in a header file (.h) *)
(* Version 1: The list of arguemetns is expanded *)
let decl_expanded b (p: xprog) =
  bprintf b "%aextern void slv6_X_%s(struct SLv6_Processor*%a);\n"
    comment p p.xprog.fid (list "" Gencxx.prog_arg) p.xgs;;

(* Version 2: The arguments are passed in a struct *)
let decl_grouped b (p: xprog) =
  bprintf b "%aextern void slv6_G_%s(struct SLv6_Processor*, struct SLv6_Instruction*);\n"
    comment p p.xprog.fid;;

(** Generation of the instruction type *)
(* Generate a type that can store an instruction 'p' *)
let inst_type b (p: xprog) =
  let field b (v, t) = bprintf b "%s %s;" t v
  in bprintf b "%astruct SLv6_%s {\n  %a\n};\n"
       comment p p.xprog.fid
       (list "\n  " field) p.xgs;;

(* Generate a member of the big union type *)
let union_field b (p: xprog) =
  bprintf b "    struct SLv6_%s %s;\n" p.xprog.fid p.xprog.fid;;

(** Generation of the decoder *)

module type DecoderConfig = sig
  (* the version, such as "decode_exec" or "decode_store" *)
  val version: string;;
  (* the profile of the main decoder function *)
  val main_prof: string;;
  (* the profile of the specific instruction decoder functions *)
  val instr_prof: Buffer.t -> string -> unit;;
  (* how to call an instruction decoder function *)
  val instr_call: Buffer.t -> string -> unit;;
  (* what we do once the instruction is decoded *)
  val action: Buffer.t -> xprog ->unit;;
  (* what we do when we return from the decoder *)
  val return_action: string;;
end;;

module DecoderGenerator (DC: DecoderConfig) = struct
  (* Generation of a decoder in a separated .c file *)
  (*  * - bn: file basename *)
  (*  * - is: the instructions *)
  let decoder bn (is: xprog list) =
    (* Phase A: check bits fixed by the coding table *)
    let instA b p =
      let (mask, value) = Gencxx.mask_value p.xprog.fdec in
      bprintf b "  if ((bincode&0x%08lx)==0x%08lx && %a) {\n"
        mask value DC.instr_call p.xprog.fid;
      bprintf b "    assert(!found); found = true;\n  }\n"
  in
    (* Phase B: extract parameters and check validity *)
  let instB b p =
    bprintf b "%astatic %a {\n"
      comment p DC.instr_prof p.xprog.fid;
    (* extract parameters *)
    let vc = Validity.vcs_to_exp p.xprog.fvcs in
      bprintf b "%a"
        (list "" (Gencxx.dec_param p.xgs vc)) p.xprog.fparams;
      (* check validity *)
      (match vc with
         | Some e -> bprintf b "  if (!(%a)) return false;\n" (exp p) e
         | None -> ());
      (* execute the instruction *)
      bprintf b "%a" DC.action p;
      bprintf b "  return true;\n}\n"
  in
  let b = Buffer.create 10000 in
    bprintf b "#include \"%s_c_prelude.h\"\n\n" bn;
    bprintf b "%a\n" (list "\n" instB) is;
    bprintf b "/* the main function, used by the ISS loop */\n";
    bprintf b "%s {\n" DC.main_prof;
    bprintf b "  bool found = false;\n";
    bprintf b "%a" (list "" instA) is;
    bprintf b "  %s}\n" DC.return_action;
    bprintf b "\nEND_SIMSOC_NAMESPACE\n";
    let outc = open_out (bn^"-"^DC.version^".c") in
      Buffer.output_buffer outc b; close_out outc;;
end;;

module DecExecConfig = struct
  let version = "decode_exec";;
  let main_prof =
    "bool decode_and_exec(struct SLv6_Processor *proc, uint32_t bincode)";;
  let instr_prof b id =
    bprintf b "bool try_exec_%s(struct SLv6_Processor *proc, uint32_t bincode)" id;;
  let instr_call b id = bprintf b "try_exec_%s(proc,bincode)" id;;
  let action b (x: xprog) =
    let aux b (s,_) = bprintf b ",%s" s in
      bprintf b "  slv6_X_%s(proc%a);\n" x.xprog.fid (list "" aux) x.xgs;;
  let return_action = "return found;"
end;;
module DecExec = DecoderGenerator(DecExecConfig);;

module DecStoreConfig = struct
  let version = "decode_store";;
  let main_prof =
    "void decode_and_store(struct SLv6_Instruction *instr, uint32_t bincode)";;
  let instr_prof b id =
    bprintf b "bool try_store_%s(struct SLv6_Instruction *instr, uint32_t bincode)" id;;
  let instr_call b id = bprintf b "try_store_%s(instr,bincode)" id;;
  let action b (x: xprog) =
    let store b (n, _) = 
      bprintf b "  instr->args.%s.%s = %s;\n" x.xprog.fid n n
    in
      if is_conditional x then (
        bprintf b "  if (cond==SLV6_AL)\n";
        bprintf b "    instr->id = SLV6_%s_NC_ID;\n" x.xprog.fid;
        bprintf b "  else\n  ");
      bprintf b "  instr->id = SLV6_%s_ID;\n" x.xprog.fid;
      bprintf b "%a" (list "" store) x.xgs;;
  let return_action = "if (!found) instr->id = SLV6_UNPRED_OR_UNDEF_ID;"
end;;
module DecStore = DecoderGenerator(DecStoreConfig);;

(** Generation of tables, all indexed by an instruction id *)
let gen_tables b (xs: xprog list) =
  let name b x = bprintf b "\n  \"%s\"" x.xprog.fname in
  let undef_name = "\n  \"Unpredictable or undefined instruction\"" in
  bprintf b "const char *slv6_instruction_names[SLV6_TABLE_SIZE] = {";
  bprintf b "%a,%s};\n\n" (list "," name) xs undef_name;
  let reference b x = bprintf b "\n  \"%s\"" x.xprog.fref in
  let undef_reference = "\n  \"no ref.\"" in
  bprintf b "const char *slv6_instruction_references[SLV6_TABLE_SIZE] = {";
  bprintf b "%a,%s};\n\n" (list "," reference) xs undef_reference;
  let fct b x = bprintf b "\n  slv6_G_%s" x.xprog.fid in
  let undef_fct = "\n  NULL" in
  bprintf b "SemanticsFunction slv6_instruction_functions[SLV6_TABLE_SIZE] = {";
  bprintf b "%a,%s};\n" (list "," fct) xs undef_fct;;

(* generate the numerical instruction identifier *)
let gen_ids b xs =
  let aux i x = bprintf b "#define SLV6_%s_ID %d\n" x.xprog.fid i in
  list_iteri aux xs;
  bprintf b "#define SLV6_UNPRED_OR_UNDEF_ID SLV6_INSTRUCTION_COUNT\n";;

(* Generation of all the semantics functions
 * - bn: file basename
 * - xs: the instructions
 * - v: a string, either "grouped" or "expanded"
 * - decl: a function, either decl_grouped or decl_expanded
 * - prog: a function, either prog_grouped or prog_expanded
 *)
let semantics_functions bn xs v decl prog =
  let bh = Buffer.create 10000 and bc = Buffer.create 10000 in
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
    (* source file *)
    bprintf bc "#include \"%s_c_prelude.h\"\n" bn;
    bprintf bc "\n%a" (list "\n" prog) xs;
    bprintf bc "\nEND_SIMSOC_NAMESPACE\n";
    let outh = open_out (bn^"_"^v^".h")
    and outc = open_out (bn^"_"^v^".c") in
      Buffer.output_buffer outh bh; close_out outh;
      Buffer.output_buffer outc bc; close_out outc;;

(** Generation of the "may branch" function *)
(* we need to find under which condition the instruction may set the PC *)

let may_branch_prog b (x: xprog) =
  let is_ldm_1 x =
    String.length x.xprog.fid >= 5 &&
      String.sub x.xprog.fid 0 5 = "LDM1_" in
  if is_ldm_1 x (* special case for LDM (1): check bit 15 of register_list *)
  then bprintf b "  case SLV6_%s_ID: return instr->args.%s.register_list>>15;\n"
    x.xprog.fid x.xbaseid
  else
    let default = (false, []) in
    let rec union l l' =
      match l with
        | hd :: tl when List.mem hd l' -> union tl l' 
        | hd :: tl -> hd :: (union tl l')
        | [] -> l' in
    let combine (b,l) (b',l') = ((b||b'), union l l') in
    let rec inst acc = function
        (* TODO: LDM(1) can be improved *)
      | Block is -> List.fold_left inst acc is
      | Affect (dst, _) -> combine acc (exp dst)
      | If (BinOp (Var "d", "==", Num "15"), i1, Some i2) -> (* case used by LDR *)
          let b,l = inst default i1 in
          let acc' = combine acc (if b then false, ["d"] else b,l) in
            inst acc' i2
      | If (_, i1, Some i2) -> inst (inst acc i1) i2
      | If (_, i, None) -> inst acc i
      | While (_, i) -> inst acc i
      | For (_, _, _, i) -> inst acc i
      | Case (_, sis) -> List.fold_left inst acc (List.map (fun (_, i) -> i) sis)
      | _ -> acc
    and exp = function
      | Reg (Var s, None)
          when s<>"i" && not (List.mem (Validity.NotPC s) x.xprog.fvcs) ->
          (false, [s])
      | Reg (Num "15", None) -> (true,[])
      | _ -> default in
    let tf,l = inst default x.xprog.finst in
      if tf
      then bprintf b "  case SLV6_%s_ID: return true;\n" x.xprog.fid
      else match l with
        | [] -> () (* bprintf b "  case SLV6_%s_ID: return false;\n" x.xprog.fid *)
        | _ ->
            let aux b s = bprintf b "instr->args.%s.%s==15" x.xbaseid s in
              bprintf b "  case SLV6_%s_ID:\n    return %a;\n"
                x.xprog.fid (list " || " aux) l;;

let may_branch b xs =
  bprintf b "bool may_branch(const struct SLv6_Instruction *instr) {\n";
  bprintf b "  switch (instr->id) {\n%a" (list "" may_branch_prog) xs;
  bprintf b "  default: return false;\n  }\n}\n";;

(** main function *)
(* bn: output file basename, pcs: pseudo-code trees, decs: decoding rules *)
let lib (bn: string) (pcs: prog list) (decs: Codetype.maplist) =
  let pcs' = List.map Gencxx.lsm_hack pcs in (* hack LSM instructions *)
  let fs: fprog list = flatten pcs' decs in
  let xs: xprog list = List.rev (List.map xprog_of fs) in
  let nocond_xs: xprog list = no_cond_variants xs in
  let all_xs: xprog list = xs@nocond_xs in
  let instr_count = List.length all_xs in
    (* create buffers for header file (bh) and source file (bc) *)
  let bh = Buffer.create 10000 and bc = Buffer.create 10000 in

    (* generate the main header file *)
    bprintf bh "#ifndef SLV6_ISS_H\n#define SLV6_ISS_H\n\n";
    bprintf bh "#include \"%s_h_prelude.h\"\n" bn;
    bprintf bh "\n#define SLV6_INSTRUCTION_COUNT %d\n" instr_count;
    bprintf bh "\n#define SLV6_TABLE_SIZE (SLV6_INSTRUCTION_COUNT+6)\n\n";
    bprintf bh "extern const char *slv6_instruction_names[SLV6_TABLE_SIZE];\n";
    bprintf bh "extern const char *slv6_instruction_references[SLV6_TABLE_SIZE];\n";
    bprintf bh "extern SemanticsFunction slv6_instruction_functions[SLV6_TABLE_SIZE];\n";
    bprintf bh "\n%a" gen_ids all_xs;
    (* generate the instruction type *)
    bprintf bh "\n%a" (list "\n" inst_type) xs;
    bprintf bh "\nstruct SLv6_Instruction {\n";
    bprintf bh "  size_t id;\n  union {\n%a" (list "" union_field) xs;
    bprintf bh "    struct ARMv6_BasicBlock *basic_block;\n";
    bprintf bh "    struct ARMv6_OptimizedBasicBlock *opt_basic_block;\n";
    bprintf bh "    struct ARMv6_SetReg set_reg;\n";
    bprintf bh "  } args;\n};\n";
    (* close the namespace (opened in ..._h_prelude.h *)
    bprintf bh "\nEND_SIMSOC_NAMESPACE\n";
    bprintf bh "\n#endif /* SLV6_ISS_H */\n";

    (* start generating the source file *)
    bprintf bc "#include \"%s_c_prelude.h\"\n" bn;
    (* generate the tables *)
    bprintf bc "\n%a" gen_tables all_xs;
    (* generate the may_branch function *)
    bprintf bc "\n%a" may_branch all_xs;
    (* close the namespace (opened in ..._c_prelude.h *)
    bprintf bc "\nEND_SIMSOC_NAMESPACE\n";
    (* write buffers to files *)
    let outh = open_out (bn^".h") and outc = open_out (bn^".c") in
      Buffer.output_buffer outh bh; close_out outh;
      Buffer.output_buffer outc bc; close_out outc;      
    (* generate the decoders *)
    DecExec.decoder bn xs;
    DecStore.decoder bn xs;
    (* Now, we generate the semantics functions. *)
    semantics_functions bn xs "expanded" decl_expanded prog_expanded;
    semantics_functions bn all_xs "grouped" decl_grouped prog_grouped;;
