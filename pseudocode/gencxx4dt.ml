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
}

let xprog_of p =
  let gs, ls = Gencxx.V.vars p.finst in
    {xprog = p; xgs = gs; xls = ls};;

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

and affect p k b dst src =
  if src = Unpredictable_exp then string b "unpredictable()"
  else match dst with
    | Reg (Var "d", _) -> bprintf b
        "set_reg_or_pc(proc,d,%a)" (exp p) src
    | Reg (Num "15", None) -> bprintf b "set_pc_raw(proc,%a)" (exp p) src
    | Reg (e, None) -> bprintf b "set_reg(proc,%a,%a)" (exp p) e (exp p) src
    | Reg (e, Some m) ->
	bprintf b "set_reg_m(proc,%a,%s,%a)" (exp p) e (Gencxx.mode m) (exp p) src
    | CPSR -> (
        match src with
          | SPSR None -> bprintf b "proc->cpsr = *spsr(proc)"
          | SPSR (Some m) -> bprintf b "proc->cpsr = *spsr_m(proc,%s)" (Gencxx.mode m)
          | _ -> bprintf b "set_StatusRegister(&proc->cpsr,%a)" (exp p) src)
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
    | Ast.Range (CPSR, Bits (n1, n2)) ->
        bprintf b "proc->cpsr.%s = %a" (Gencxx.cpsr_field (n1,n2)) (exp p) src
    | Ast.Range (e1, Bits (n1, n2)) ->
        inst_aux p k b (Proc ("set_field", [e1; Num n1; Num n2; src]))
    | Memory (addr, n) ->
        inst_aux p k b (Proc ("write_" ^ Gencxx.access_type n, [addr; src]))
    | Ast.Range (e, Index n) -> inst_aux p k b (Proc ("set_bit", [e; n; src]))
    | _ -> string b "TODO(\"affect\")";;


let comment b p = bprintf b "/* %s\n * %s */\n" p.xprog.fref p.xprog.fname;;

(* Defintion of the functions. This should be printed in a source file (.c) *)
let prog b (p: xprog) =
  let ss = List.fold_left (fun l (s, _) -> s::l) [] p.xgs in
  let inregs = List.filter (fun x -> List.mem x Gencxx.input_registers) ss in
    bprintf b "%avoid %s(struct SLv6_Processor *proc%a)\n{\n%a%a%a\n}\n" comment p
      p.xprog.fid
      (list "" Gencxx.prog_arg) p.xgs
      (list "" Gencxx.inreg_load) inregs
      (list "" Gencxx.local_decl) p.xls
      (inst p 2) p.xprog.finst;;

(* Declaration of the functions. This should be printed in a header file (.h) *)
let decl b (p: xprog) =
  bprintf b "%aextern void %s(struct SLv6_Processor*%a);\nextern bool try_%s(struct SLv6_Processor*, uint32_t bincode);\n"
    comment p p.xprog.fid
    (list "" Gencxx.prog_arg) p.xgs p.xprog.fid;;

(** Generation of the decoder *)
let dec_inst b (is: xprog list) =
  (* Phase A: check bits fixed by the coding table *)
  let instA b p =
    let (mask, value) = Gencxx.mask_value p.xprog.fdec in
      bprintf b "  if ((bincode&0x%08lx)==0x%08lx && try_%s(proc,bincode)) {\n"
        mask value p.xprog.fid;
      bprintf b "    DEBUG(puts(\"decoder choice: %s\"));\n" p.xprog.fid;
      bprintf b "    assert(!found); found = true;\n  }\n"
  in
    (* Phase B: extract parameters and check validity *)
  let instB b p =
    bprintf b "bool try_%s(struct SLv6_Processor *proc, uint32_t bincode) {\n"
      p.xprog.fid;
    (* extract parameters *)
    let vc = Validity.vcs_to_exp p.xprog.fvcs in
      bprintf b "%a"
        (list "" (Gencxx.dec_param p.xgs vc)) p.xprog.fparams;
      (* check validity *)
      (match vc with
         | Some e -> bprintf b "  if (!(%a)) return false;\n" (exp p) e
         | None -> ());
      (* execute the instruction *)
      let aux b (s,_) = bprintf b ",%s" s in
        bprintf b "  EXEC(%s(proc%a));\n" p.xprog.fid (list "" aux) p.xgs;
        bprintf b "  return true;\n}\n"
  in
  let is' = List.rev is in
    bprintf b "bool decode_and_exec(struct SLv6_Processor *proc, uint32_t bincode) {\n";
    bprintf b "  bool found = false;\n";
    bprintf b "%a" (list "" instA) is';
    bprintf b "  return found;\n}\n\n%a"
      (list "\n" instB) is';;

(* main function
 * bn: output file basename, pcs: pseudo-code trees, decs: decoding rules *)
let lib (bn: string) (pcs: prog list) (decs: Codetype.maplist) =
  let pcs' = List.map Gencxx.lsm_hack pcs in (* hack LSM instructions *)
  let fs: fprog list = flatten pcs' decs in
  let xs: xprog list = List.map xprog_of fs in
    (* create buffers for header file (bh) and source file (bc) *)
  let bh = Buffer.create 10000 and bc = Buffer.create 10000 in
    (* generate the header file *)
    bprintf bh "#ifndef ARM_ISS_H\n#define ARM_ISS_H\n\n";
    bprintf bh "#include \"slv6_iss_h_prelude.h\"\n\n";
    bprintf bh "%a" (list "\n" decl) xs;
    bprintf bh "\nextern bool decode_and_exec(struct SLv6_Processor*, uint32_t bincode);\n";
    bprintf bh "\nEND_SIMSOC_NAMESPACE\n";
    bprintf bh "\n#endif /* ARM_ISS_H */\n";
    (* generate the source file *)
    bprintf bc "#include \"%s.h\"\n#include \"slv6_iss_c_prelude.h\"\n\n%a\n%a"
      bn (list "\n" prog) xs dec_inst xs;
    bprintf bc "\nEND_SIMSOC_NAMESPACE\n";
    (* write buffers to files *)
    let outh = open_out (bn^".h") and outc = open_out (bn^".c") in
      Buffer.output_buffer outh bh; close_out outh;
      Buffer.output_buffer outc bc; close_out outc;;
