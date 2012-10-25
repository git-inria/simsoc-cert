(**
SimSoC-Cert, a toolkit for generating certified processor simulators
See the COPYRIGHTS and LICENSE files.

Generation of the ASM printers.
*)

module Make (Gencxx : Gencxx.GENCXX) = 
struct

module Sl2_patch = Sl2_patch.Make (Gencxx)

open Util;;
open Flatten;;
open Syntaxtype;;
open Printf;;
open Sl2_patch;;

(* TODO: Thumb BL, BLX(1) instruction *) 

module type PrinterConfig = sig
  val out: string;;
  val printer_args: string;;
  val string: Buffer.t -> string -> unit;;
  val char: Buffer.t -> char ->unit;;
  val dstring: Buffer.t -> (Buffer.t -> xprog -> unit) -> xprog -> unit;;
  val dchar: Buffer.t -> (Buffer.t -> xprog -> unit) -> xprog -> unit;;
  val dinthex: Buffer.t -> (Buffer.t -> xprog -> unit) -> xprog -> unit;;
  val dintdec: Buffer.t -> (Buffer.t -> xprog -> unit) -> xprog -> unit;;
  val dint_0is32: Buffer.t -> (Buffer.t -> xprog -> unit) -> xprog -> unit;;
end;;

module CPrinterConfig = struct
  let out = "f";;
  let printer_args = "FILE *f, struct SLv6_Instruction *instr, uint32_t bincode";;
  let string b s = bprintf b "  fprintf(f,\"%s\");\n" (String.escaped s);;
  let char b c = bprintf b "  fputc('%c',f);\n" c;;
  let dstring b f x = bprintf b "  fprintf(f,\"%%s\",%a);\n" f x;;
  let dchar b f x = bprintf b "  fprintf(f,\"%%c\",%a);\n" f x;;
  let dinthex b f x = bprintf b "  fprintf(f,\"0x%%x\",%a);\n" f x;;
  let dintdec b f x = bprintf b "  fprintf(f,\"%%d\",%a);\n" f x;;
  let dint_0is32 b f x = bprintf b "  fprintf(f,\"%%d\",(%a ? %a : 32));\n" f x f x;;
end;;

module CxxPrinterConfig = struct
  let out = "os";;
  let printer_args =
    "std::ostream &os, struct SLv6_Instruction *instr, uint32_t bincode";;
  let string b s = bprintf b "  os <<\"%s\";\n" (String.escaped s);;
  let char b c = bprintf b "  os <<'%c';\n" c;;
  let dstring b f x = bprintf b "  os <<(%a);\n" f x;;
  let dchar = dstring;;
  let dinthex b f x = bprintf b "  os <<std::hex <<(uint32_t)(%a);\n" f x;;
  let dintdec b f x = bprintf b "  os <<std::dec <<(int32_t)(%a);\n" f x;;
  let dint_0is32 b f x = bprintf b "  os <<std::dec <<(%a ? %a : 32);\n" f x f x;;
end;;

module Printer (PC: PrinterConfig) = struct

  let param s b x =
    if x.xprog.finstr = "BKPT" && s = "immed_16" then
      bprintf b "(get_bits(bincode,19,8)<<4)|get_bits(bincode,3,0)"
    else if List.mem_assoc s x.xips then bprintf b "instr->args.%s.%s" (union_id x) s
    else
      let _s, x, y = try List.find (fun (s',_,_) -> s = s') x.xprog.fparams
      with Not_found -> raise (Invalid_argument ("no parameter named \""^s^
                                                   "\" in "^x.xprog.fid))
      in if x = y then bprintf b "get_bit(bincode,%d)" x
        else bprintf b "get_bits(bincode,%d,%d)" x y;;
  
  let mode b x = bprintf b "  slv6_print_mode(%s,%a);\n" PC.out (param "mode") x;;
  
  let target_address b x s =
    bprintf b "  if (%a>>31) {\n  " (param s) x;
    PC.string b "PC-#"; bprintf b "  ";
    let aux b x = bprintf b "-%a" (param s) x in
      PC.dinthex b aux x; bprintf b "  } else {\n  ";
      PC.string b "PC+#"; PC.dinthex b (param s) x;
      bprintf b "  }\n";;

  let printer b (x: xprog) =
    let token b = function
      | Const s -> PC.string b s
      | Param p -> (
          match p with
              (* registers *)
            | "Rd" | "Rn" | "Rs" | "Rm" | "RdLo" | "RdHi" ->
                let p' = String.sub p 1 (String.length p - 1)
                in bprintf b "  slv6_print_reg(%s,%a);\n" PC.out (param p') x
            | "CRd" | "CRn" | "CRm" -> PC.string b "CR"; PC.dintdec b (param p) x
                (* REMARK: some examples if the manual use "c" instead of "CR" *)
                
            (* immediate values *)
            | "immed_16" | "immed_24" | "offset_12"
            | "immed_3" | "immed_8" | "immed_7" | "immed_5" -> PC.dinthex b (param p) x
            | "opcode_1" | "opcode_2" | "opcode" -> PC.dintdec b (param p) x
            | "shift_imm" -> PC.dint_0is32 b (param p) x
                
            (* special cases *)
            | "offset_8" -> (
                try let b' = Buffer.create 32 in
                  PC.dinthex b' (param p) x; bprintf b "%s" (Buffer.contents b')
                with Invalid_argument _ -> PC.dinthex b (param "immedHL") x)
            | "target_address" when x.xprog.fkind = ARM -> (* B, BL *)
                target_address b x "pc_offset"
            | "target_addr" when x.xprog.fkind = ARM -> (* BLX(1) *)
                target_address b x "pc_offset_h"
            | "target_address" when x.xprog.finstr = "Tb_B1" ->
                target_address b x "simmed_8_ext"
            | "target_address" when x.xprog.finstr = "Tb_B2" ->
                target_address b x "simmed_11_ext"
            | "target_addr" -> (* Thumb BL, BLX(1) *)
                raise (Failure "Thumb BL, BLX(1) requires a special function")
            | "coproc" -> PC.string b "p"; PC.dintdec b (param "cp_num") x
            | "effect" -> (* CPS x2 *)
                let (y, z) = match x.xprog.fkind with ARM -> (2,3) | Thumb -> (0,1) in
                  bprintf b "  if (%a==%d)" (param "imod") x y; PC.string b "IE";
                  bprintf b "  else if (%a==%d)" (param "imod") x z; PC.string b "ID";
            | "iflags" -> (* CPS x2 *)
                bprintf b "  if (%a)" (param "A") x; PC.char b 'a';
                bprintf b "  if (%a)" (param "I") x; PC.char b 'i';
                bprintf b "  if (%a)" (param "F") x; PC.char b 'f'
            | "mode" -> (* CPS, SRS *) mode b x
            | "registers" when x.xprog.fid = "Tb_PUSH" -> (* add LR if R *)
                bprintf b "  slv6_print_reglist(%s,%a|((uint16_t)%a<<14));\n"
                  PC.out (param "register_list") x (param "R") x
            | "registers" when x.xprog.fid = "Tb_POP" -> (* add PC if R *)
                bprintf b "  slv6_print_reglist(%s,%a|((uint16_t)%a<<15));\n"
                  PC.out (param "register_list") x (param "R") x
            | "registers" | "registers_without_pc" | "registers_and_pc" -> (* LSM *)
                bprintf b "  slv6_print_reglist(%s,%a);\n"
                  PC.out (param "register_list") x
            | "fields" -> (* MSRimm, MSRreg *)
                bprintf b "  if (%a&1)" (param "field_mask") x; PC.char b 'c';
                bprintf b "  if (%a&2)" (param "field_mask") x; PC.char b 'x';
                bprintf b "  if (%a&4)" (param "field_mask") x; PC.char b 's';
                bprintf b "  if (%a&8)" (param "field_mask") x; PC.char b 'f'
            | "endian_specifier" -> (* SETEND *)
                let aux b x = bprintf b "(%a ? \"BE\" : \"LE\")" (param "E") x
                in PC.dstring b aux x
            | "x" | "y" -> (* SMLA<x><y>, SMLAL<x><y>, ... *)
                let aux b x = bprintf b "(%a ? 'T' : 'B')" (param p) x in
                  PC.dchar b aux x
            | "immed" -> (* SSAT, SSAT16 *) PC.dintdec b (param "sat_imm") x
            | "immediate" -> (* *_M1_Imm *) PC.dinthex b (param "immed_rotated") x
            | "option" -> PC.string b "{"; PC.dinthex b (param p) x; PC.string b "}"
            | "cond" -> bprintf b "  slv6_print_cond(%s,%a);\n" PC.out (param "cond") x
                
            | _ -> (* Nothing should remain *)
                raise (Failure ("Printing Param: "^p)))
          
      | OptParam (p, None) -> (
          match p with
            | "S" | "L" | "X" | "R" ->
                bprintf b "  if (%a)" (param p) x; PC.char b p.[0]
            | "!" -> bprintf b "  if (%a)" (param "W") x; PC.char b '!'
                
            | _ ->  (* Nothing should remain *)
                raise (Failure ("Printing Opt: "^p)))
          
      | OptParam (s, Some p) -> (
          match p with
            | "cond" ->
                bprintf b "  if (%a!=0xe) slv6_print_cond(%s,(SLv6_Condition)%a);\n"
                (param "cond") x PC.out (param "cond") x
            | "mode" -> (* CPS *)
                bprintf b "  if (%a) {\n  " (param "mmod") x;
                PC.string b s; bprintf b "  "; mode b x; bprintf b "  }\n"
            | "opcode_2" ->
                bprintf b "  if (%a) {\n  " (param p) x; PC.string b s;
                bprintf b "  "; PC.dintdec b (param p) x; bprintf b "  }\n"
            | "shift_imm" when x.xprog.finstr = "PKHBT" ->
                bprintf b "  if (%a) {\n  " (param "shift_imm") x; PC.string b s;
                bprintf b "  "; PC.dintdec b (param "shift_imm") x; bprintf b "  }\n"
            | "shift_imm" when x.xprog.finstr = "PKHTB" ->
                PC.string b s; PC.dint_0is32 b (param "shift_imm") x
            | "shift" -> (* SSAT, USAT *)
                bprintf b "  if (%a) {\n  " (param "shift") x;
                PC.string b s; bprintf b "  "; PC.string b "  ASR #"; bprintf b "  ";
                PC.dint_0is32 b (param "shift_imm") x;
                bprintf b "  } else if (%a) {\n  " (param "shift_imm") x;
                PC.string b s; bprintf b "  "; PC.string b "  LSL #"; bprintf b "  ";
                PC.dintdec b (param "shift_imm") x; bprintf b "  }\n"
            | "rotation" -> (* SXT*, UXT* *)     
                bprintf b "  if (%a) {\n  " (param "rotate") x;
                PC.string b (s^"ROR #"); bprintf b "  ";
                let aux b x = bprintf b "(%a)*8" (param "rotate") x in
                  PC.dintdec b aux x; bprintf b "  }\n"
                                                                         
            | _ -> (* Nothing should remain *)
                raise (Failure ("Printing OptParam: "^p)))
          
      | PlusMinus -> 
          let aux b x = bprintf b "(%a ? '+' : '-')" (param "U") x in PC.dchar b aux x
    in
      if x.xprog.finstr = "Tb_BL" then (
        bprintf b "void slv6_P_%s(%s) {\n" x.xprog.fid PC.printer_args;
        PC.string b "BL, BLX(1): prefix or suffix"; (* FIXME *)
        bprintf b "}\n"
      ) else (
        bprintf b "void slv6_P_%s(%s) {\n" x.xprog.fid PC.printer_args;
        ( match x.xprog.fsyntax with
            | [] -> raise (Invalid_argument "printer: empty variant list")
            | [v] -> bprintf b "%a" (list token) v
            | [c; nc] when List.mem (Param "coproc") c ->
                bprintf b "if (bincode>>28==0xf) {\n%a} else {\n%a}\n"
                  (list token) nc (list token) c
            | [e; ne] when x.xprog.fid = "CPS" ->
                bprintf b "if (%a<=1) {\n%a} else {\n%a}\n" (param "imod") x
                  (list token) ne (list token) e
            | [ll; lr; ar; rr; rx] ->
                bprintf b "switch (%a) {\n" (param "shift") x;
                bprintf b "case 0: {\n%a} return;\n" (list token) ll;
                bprintf b "case 1: {\n%a} return;\n" (list token) lr;
                bprintf b "case 2: {\n%a} return;\n" (list token) ar;
                bprintf b "case 3: if (%a) {\n%a} else {\n%a} return;\n"
                  (param "shift_imm") x (list token) rr (list token) rx;
                bprintf b "}\n"
            | [cpsr; spsr] when List.mem x.xprog.fid ["MRS"; "MSRimm"; "MSRreg"] ->
                bprintf b "if (%a) {\n%a} else {\n%a}\n" (param "R") x
                  (list token) spsr (list token) cpsr              
            | _ -> raise (Failure ("case not implemented: "^x.xprog.fid)));
        bprintf b "}\n"
      );;
end;;

module CPrinter = Printer(CPrinterConfig);;
module CxxPrinter = Printer(CxxPrinterConfig);;

let c_printers bn xs =
  let printer_args = CPrinterConfig.printer_args in
    ( let bh = Buffer.create 10000 in
        bprintf bh "#ifndef %s_PRINTERS_H\n#define %s_PRINTERS_H\n\n" bn bn;
        bprintf bh "#include <stdio.h>\n#include \"%s.h\"\n\n" bn;
        bprintf bh "typedef void (*PrintFunction)(%s);\n" printer_args;
        bprintf bh "extern PrintFunction slv6_printers[SLV6_TABLE_SIZE];\n\n";
        bprintf bh "extern void slv6_print_instr(%s);\n\n" printer_args;
        bprintf bh "#endif /* %s_PRINTERS_H */\n" bn;
        let outh = open_out (bn^"_printers.h") in
          Buffer.output_buffer outh bh; close_out outh
    );
    ( let bc = Buffer.create 10000
      and aux b x = bprintf b "\n  slv6_P_%s" x.xprog.fid in
        bprintf bc "#include \"%s_printers.h\"\n" bn;
        bprintf bc "#include \"slv6_math.h\"\n";
        bprintf bc "#include \"slv6_processor.h\"\n\n";
        bprintf bc "%a\n" (list_sep "\n" CPrinter.printer) xs;
        bprintf bc "PrintFunction slv6_printers[SLV6_TABLE_SIZE] = {%a};\n\n"
          (list_sep "," aux) xs;
        bprintf bc "void slv6_print_instr(%s) {\n" printer_args;
        bprintf bc "  assert(instr->args.g0.id<SLV6_TABLE_SIZE);\n";
        bprintf bc "  slv6_printers[instr->args.g0.id](f,instr,bincode);\n}\n";
        let outc = open_out (bn^"_printers.c") in
          Buffer.output_buffer outc bc; close_out outc
    );;

let cxx_printers bn xs =
  let printer_args = CxxPrinterConfig.printer_args in
    ( let bh = Buffer.create 10000 in
        bprintf bh "#ifndef %s_PRINTERS_HPP\n#define %s_PRINTERS_HPP\n\n" bn bn;
        bprintf bh "#include <ostream>\n#include \"%s.h\"\n\n" bn;
        bprintf bh "namespace simsoc {\n\n";
        bprintf bh "  typedef void (*PrintFunction)(%s);\n" printer_args;
        bprintf bh "  extern PrintFunction slv6_printers[SLV6_TABLE_SIZE];\n\n";
        bprintf bh "  extern void slv6_print_instr(%s);\n\n" printer_args;
        bprintf bh "} // namespace simsoc\n\n";
        bprintf bh "#endif // %s_PRINTERS_HPP\n" bn;
        let outh = open_out (bn^"_printers.hpp") in
          Buffer.output_buffer outh bh; close_out outh
    );
    ( let bc = Buffer.create 10000
      and aux b x = bprintf b "\n  slv6_P_%s" x.xprog.fid in
        bprintf bc "#include \"%s_printers.hpp\"\n" bn;
        bprintf bc "#include \"slv6_math.h\"\n";
        bprintf bc "#include \"slv6_processor.h\"\n\n";
        bprintf bc "namespace simsoc {\n\n";
        bprintf bc "extern void slv6_print_cond(std::ostream&, SLv6_Condition);\n";
        bprintf bc "extern void slv6_print_mode(std::ostream&, SLv6_Mode);\n";
        bprintf bc "extern void slv6_print_reg(std::ostream&, uint8_t);\n\n";
        bprintf bc "extern void slv6_print_reglist(std::ostream&, uint16_t);\n\n";
        bprintf bc "%a\n" (list_sep "\n" CxxPrinter.printer) xs;
        bprintf bc "PrintFunction slv6_printers[SLV6_TABLE_SIZE] = {%a};\n\n"
          (list_sep "," aux) xs;
        bprintf bc "void slv6_print_instr(%s) {\n" printer_args;
        bprintf bc "  assert(instr->args.g0.id<SLV6_TABLE_SIZE);\n";
        bprintf bc "  slv6_printers[instr->args.g0.id](os,instr,bincode);\n}\n\n";
        bprintf bc "} // namespace simsoc\n";
        let outc = open_out (bn^"_printers.cpp") in
          Buffer.output_buffer outc bc; close_out outc
    );;

let printers bn xs = c_printers bn xs; cxx_printers bn xs;;

end
