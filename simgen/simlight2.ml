(**
SimSoC-Cert, a toolkit for generating certified processor simulators
See the COPYRIGHTS and LICENSE files.

   Generate additional C/C++ code for implementing dynamic translation in
   Simlight.
*)

(* Transformation flow:
   
   In general, patch functions are in sl2_patch.ml, and generation
   functions are in this file.
   
   At the beginning, we have one list of progs (cf ast.ml) and another list of
   coding tables (cf codetype.ml). There is a third list describing the ASM
   syntax (cf syntaxtype.ml). Each list item describes either an instruction or
   an addressing mode case.
   
   - MSR is splitted in MSRreg and MSRimm (cf file norm.ml)
   - the pseudo-code is normalized (cf file norm.ml)
   - the address write-back is disabled in the M2, M3, and M4 addressing modes
   - the 3-uplets <instruction, addressing mode case, syntax> are flattened
   (cf file flatten.ml)
     o during flattening, some patches are applied:
       patch_W, patch_SRS, patch SRS_RFE

   From this point, we manipulate "flat programs" (cf flatten.ml). The
   notion of addressing mode has disappeared.

   - We remove the Thumb instruction MOV(3), because it is identical to CPY
   - Where possible, we swap the conjunctions so that the CP15 U bit is tested
     after the alignment. This is an optimization try, maybe useless.
   - We improve the instructions that use the coprocessor
     (+ disable LDC and STC).
   - We fix a problem about "address of next instruction".
   - We compute the list of parameters and variables used by the pseudo-code
   - We replace some sub-expressions by "computed parameters"
   - We remove the ConditionPassed tests
   - We insert the writebacks at the end of the instructions
     (previously removed from the addressing mode cases)
   - We specialize the instructions for some boolean parameter values
   - We compute the list of instruction groups. All instructions in a group
     have the same list of parameters
   
   From this point, we manipulate extended programs; i.e., flat program with 
   symbol tables.

   - We create the unconditional variants of the conditional instructions

   Now, the code generation can start.

   - We generate the instruction type and sub-types.
   - We generate the tables containing, among other things, the instruction
     names
   - We generate the may_branch function
   - We generate the 4 decoders: {thumb, arm32} x {decode_and_store,
     decode_and_exec} (cf sl2_decoder.ml)
   - We generate a small program, which is used only to control the size of the
     instruction type
   - We generate (part of) the ARM to LLVM translator
   - We generate the ASM printers. We need 2 versions:
     o one C version using fprintf and FILE*
     o one C++ version using streams 
   - We generate the semantics function (cf sl2_semantics.ml).
     We need 2 versions:
     o one version with an expanded list of atomic arguments
     o one version taking an SLv6_Instruction* as argument
*)

open Ast;;
open Util;;
open Printf;;
open Dec;;
open Codetype;;
open Syntaxtype;;
open Flatten;;
open Sl2_patch;;
open Sl2_semantics;;
open Sl2_decoder;;
open Sl2_print;;

(** Generation of the instruction type *)

(* Generate a type that can store an instruction of group g *)
let group_type b (g: group) =
  let n, ps = g in
  let field b (v, t) = bprintf b "  %s %s;\n" t v
  in bprintf b "/* Instruction Group #%d */\nstruct SLv6_g%d {\n  uint16_t id;\n%a};\n"
       n n (list field) ps;;

(* Generate a member of the big union type *)
let union_field b (g: group) =
  let n, _ = g in bprintf b "    struct SLv6_g%d g%d;\n" n n;;

(** Generation of tables, all indexed by an instruction id *)
let gen_tables b (xs: xprog list) =
  let name b x = bprintf b "\n  \"%s\"" x.xprog.fname in
  let undef_name = "\n  \"Unpredictable or undefined instruction\"" in
  bprintf b "const char *slv6_instruction_names[SLV6_TABLE_SIZE] = {";
  bprintf b "%a,%s};\n\n" (list_sep "," name) xs undef_name;
  let reference b x = bprintf b "\n  \"%s\"" x.xprog.fref in
  let undef_reference = "\n  \"no ref.\"" in
  bprintf b "const char *slv6_instruction_references[SLV6_TABLE_SIZE] = {";
  bprintf b "%a,%s};\n\n" (list_sep "," reference) xs undef_reference;
  let fct b x = bprintf b "\n  slv6_G_%s" x.xprog.fid in
  let undef_fct = "\n  NULL" in
  bprintf b "SemanticsFunction slv6_instruction_functions[SLV6_TABLE_SIZE] = {";
  bprintf b "%a,%s};\n" (list_sep "," fct) xs undef_fct;;

(* generate the numerical instruction identifier *)
let gen_ids b xs =
  let aux i x =
    bprintf b "#define SLV6_%s_ID %d\n" x.xprog.fid i;
    bprintf b "#define SLV6_%s_GID g%d\n" x.xprog.fid x.xgid
  in
  list_iteri aux xs;
  bprintf b "#define SLV6_UNPRED_OR_UNDEF_ID SLV6_INSTRUCTION_COUNT\n";;

(** Generation of the "may branch" function *)
(* we need to find under which condition the instruction may set the PC *)

let may_branch_prog b (x: xprog) =
  (* special case for LDM (1): check bit 15 of register_list *)
  if x.xprog.finstr = "LDM1" then
    bprintf b "  case SLV6_%s_ID: return instr->args.%s.register_list>>15;\n"
      x.xprog.fid (union_id x)
  (* special case for POP: check bit R *)
  else if x.xprog.finstr = "Tb_POP" then
    bprintf b "  case SLV6_%s_ID: return instr->args.%s.R==1;\n"
      x.xprog.fid (union_id x)
  (* special case for BL, BLX (1): check filed H *)
  else if x.xprog.finstr = "Tb_BL" then
    bprintf b "  case SLV6_%s_ID: return instr->args.%s.H!=2;\n"
      x.xprog.fid (union_id x)
  (* special case for CPS: clearing bit F or I may raise an interrupt *)
  else if x.xprog.finstr = "CPS" then (
    bprintf b "  case SLV6_CPS_ID:\n";
    bprintf b
      "    return (instr->args.%s.F || instr->args.%s.I) && instr->args.%s.imod==2;\n"
      (union_id x) (union_id x) (union_id x))
  (* special case for MSR*: modifying bit F or I may raise an interrupt *)
  else if x.xprog.finstr = "MSRimm" then
    bprintf b "  case SLV6_%s_ID: return instr->args.%s.field_mask&1;\n"
      x.xprog.fid (union_id x)
  else if x.xprog.finstr = "MSRreg" then
    bprintf b "  case SLV6_%s_ID: return instr->args.%s.field_mask&1;\n"
      x.xprog.fid (union_id x)
  (* special case for MCR[R]: modifying the system coprocessor state may have special effects *)
  else if x.xprog.finstr = "MCR" || x.xprog.finstr = "MCRR" then
    bprintf b "  case SLV6_%s_ID: return instr->args.%s.cp_num==15;\n"
      x.xprog.fid (union_id x)
  else
    let default = (false, []) in
    let rec union l l' =
      match l with
        | hd :: tl when List.mem hd l' -> union tl l' 
        | hd :: tl -> hd :: (union tl l')
        | [] -> l' in
    let combine (b,l) (b',l') = ((b||b'), union l l') in
    let rec inst acc = function
      | Block is -> List.fold_left inst acc is
      | Assign (dst, _) -> combine acc (exp dst)
      | If (BinOp (Var "d", "==", Num "15"), i1, Some i2) ->
          (* case used by LDR (i1) and MRC (i2) *)
          let b1,l1 = inst default i1 in
          let acc1 = combine acc (if b1 then false, ["d"] else b1,l1) in
          let b2,l2 = inst default i2 in
            combine acc1 (b2, List.filter (fun x -> x<>"d") l2)
      | If (_, i1, Some i2) -> inst (inst acc i1) i2
      | If (_, i, None) -> inst acc i
      | While (_, i) -> inst acc i
      | For (_, _, _, i) -> inst acc i
      | Case (_, sis, oi) -> List.fold_left inst acc 
	(let sis = List.map snd sis in
	 match oi with None -> sis | Some i -> sis @ [ i ])
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
            let aux b s = bprintf b "instr->args.%s.%s==15" (union_id x) s in
              bprintf b "  case SLV6_%s_ID:\n    return %a;\n"
                x.xprog.fid (list_sep " || " aux) l;;

let may_branch b xs =
  bprintf b "bool may_branch(const struct SLv6_Instruction *instr) {\n";
  bprintf b "  switch (instr->args.g0.id) {\n%a" (list may_branch_prog) xs;
  bprintf b "  case SLV6_UNPRED_OR_UNDEF_ID: return true;\n";
  bprintf b "  default: return false;\n  }\n}\n";;

(** print sizeof(T) for each instruction type T *)

let dump_sizeof bn gs =
  let b = Buffer.create 10000 in
  let aux b (n,_) =
    bprintf b "  printf(\"%%2ld SLv6_g%d\\n\", sizeof(struct SLv6_g%d));\n" n n
  in
    bprintf b "#include \"%s.h\"\n" bn;
    bprintf b "#include <stdio.h>\n\n";
    bprintf b "int main(int argc, char *argv[]) {\n";
    bprintf b "%a" (list aux) gs;
    bprintf b
      "  printf(\"%%2ld SLv6_Instruction\\n\", sizeof(struct SLv6_Instruction));\n";
    bprintf b "  return 0;\n}\n";
    let out = open_out ("print_sizes.c") in
      Buffer.output_buffer out b; close_out out;;

(** Generation of the LLVM generator *)

(* We generate only the function "generate_one_instruction",
   which is included in the file "arm_v6_llvm_generator.cpp".
   The generated file cannot be compiled outside SimSoC. *)

let llvm_generator bn xs =
  let case b (x: xprog) = 
    bprintf b "  case SLV6_%s_ID: {\n" x.xprog.fid;
    bprintf b "    Function *fct = module->getFunction(\"slv6_X_%s\"); assert(fct);\n"
      x.xprog.fid;
    let args = x.xips in
    let size = 1 + List.length args in
    let name b (n,_) = bprintf b "%s" n in
    let value b (n,t) =
      let llvm_type = function
        | "uint8_t" | "bool" -> "i8"
        | "uint16_t" -> "i16"
        | "uint32_t" | "SLv6_Condition" | "SLv6_Mode" -> "i32"
        | s -> raise (Invalid_argument ("llvm_type: "^s))
      in
        bprintf b "    Value *%s = ConstantInt::get(%s,instr.args.%s.%s);\n"
          n (llvm_type t) (union_id x) n
    in
      if size = 1 then bprintf b "    IRB.CreateCall(fct,proc);\n"
      else (
        bprintf b "%a" (list value) args;
        if size<=4 then 
          bprintf b "    IRB.CreateCall%d(fct,proc,%a);\n"
            size (list_sep "," name) args
        else (
          bprintf b "    Value *args[%d] = {proc,%a};\n"
            size (list_sep "," name) args;
          bprintf b "    IRB.CreateCall<Value**>(fct,args,args+%d);\n" size)
      );
    bprintf b "  } break;\n";
  in let b = Buffer.create 10000 in
    bprintf b "void ARMv6_LLVM_Generator::generate_one_instruction";
    bprintf b "(SLv6_Instruction &instr) {\n";
    bprintf b "  switch (instr.args.g0.id) {\n%a  default: abort();\n  }\n}\n"
      (list case) xs;
  let out = open_out (bn^"-llvm_generator.hpp") in
    Buffer.output_buffer out b; close_out out;;

(* temporary functions *)

let print_stat k xs =
  let size = match k with ARM -> 32 | Thumb -> 16 in
    for i = 0 to size-1 do
      let v = ref 0 and p = ref 0 and r = ref 0 and s = ref 0 in
      let aux x = match x.xprog.fdec.(i) with
        | Value _ -> v := !v + 1
        | Param1 _ | Param1s _ -> p := !p + 1
        | Range _ -> r := !r + 1
        | Shouldbe _ -> s := !s + 1
        | _ -> ()
      in List.iter aux xs;
        printf "Bit %2d: %3d V, %3d P, %3d R, %3d S\n"  i !v !p !r !s
    done;;

(** main function *)

(* bn: output file basename, pcs: pseudo-code trees, decs: decoding rules *)
let lib (bn: string) ({ body = pcs ; _ } : program) (ss: syntax list)
    (decs: Codetype.maplist) (wf: string option) =
  let pcs': prog list = postpone_writeback pcs in
  let fs4: fprog list = List.rev (flatten pcs' ss decs) in
    (* remove MOV (3) thumb instruction, because it is redundant with CPY. *)
  let fs3: fprog list = List.filter (fun f -> f.fid <> "Tb_MOV3") fs4 in
  let fs2: fprog list = List.map swap_u_test fs3 in
  let fs1: fprog list = List.map patch_coproc fs2 in
  let fs: fprog list = List.map patch_addr_of_next_instr fs1 in
  let (xs: xprog list), (groups: group list) = xprogs_of fs wf in
  let var_xs: xprog list = restricted_variants xs in
  let all_xs: xprog list =
    assert (wf <> None || var_xs = []); xs @ var_xs in
  let instr_count = List.length all_xs in
    (* create buffers for header file (bh) and source file (bc) *)
  let bh = Buffer.create 10000 and bc = Buffer.create 10000 in

    (* generate the main header file *)
    bprintf bh "#ifndef SLV6_ISS_H\n#define SLV6_ISS_H\n\n";
    bprintf bh "#include \"%s_h_prelude.h\"\n" bn;
    (match wf with Some _ -> bprintf bh "\n#define SLV6_USE_WEIGHTS 1\n" | None -> ());
    bprintf bh "\n#define SLV6_INSTRUCTION_COUNT %d\n" instr_count;
    bprintf bh "\n#define SLV6_TABLE_SIZE (SLV6_INSTRUCTION_COUNT+11)\n\n";
    bprintf bh "extern const char *slv6_instruction_names[SLV6_TABLE_SIZE];\n";
    bprintf bh "extern const char *slv6_instruction_references[SLV6_TABLE_SIZE];\n";
    bprintf bh "extern SemanticsFunction slv6_instruction_functions[SLV6_TABLE_SIZE];\n";
    bprintf bh "\n%a" gen_ids all_xs;
    (* generate the instruction type *)
    bprintf bh "\n%a" (list_sep "\n" group_type) groups;
    bprintf bh "\nstruct SLv6_Instruction {\n";
    bprintf bh "  SemanticsFunction sem_fct;\n";
    bprintf bh "  union {\n%a" (list union_field) groups;
    bprintf bh "    struct ARMv6_InstrBasicBlock basic_block;\n";
    bprintf bh "    struct ARMv6_InstrOptimizedBasicBlock opt_basic_block;\n";
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
    let arm_xs, thumb_xs = List.partition (fun x -> is_arm x.xprog) xs in
      DecExec.decoder bn ARM arm_xs;
      DecStore.decoder bn ARM arm_xs;
      DecExec.decoder bn Thumb thumb_xs;
      DecStore.decoder bn Thumb thumb_xs;
      (* print_stat ARM arm_xs; *)
      (* print_stat Thumb thumb_xs; *)
    (* generate a small program to verify the sizes of the instruciton types *)
    dump_sizeof bn groups;
    (* generate the LLVM generator (mode DT3) *)
    llvm_generator bn all_xs;
    (* generate the ASM printers *)
    printers bn all_xs;
    (* Now, we generate the semantics functions. *)
    semantics_functions bn all_xs "expanded" decl_expanded prog_expanded;
    semantics_functions bn all_xs "grouped" decl_grouped prog_grouped;;
