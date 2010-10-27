(**
SimSoC-Cert, a library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Generation of the ASM printers.
*)

open Util;;
open Flatten;;
open Syntaxtype;;
open Printf;;
open Sl2_patch;;

(* TODO: Thumb BL, BLX(1) instruction *) 

(* TODO: variant selection *)

let string b s = bprintf b "  fprintf(f,\"%s\");\n" s;;

let dstring b f x = bprintf b "  fprintf(f,\"%%s\",%a);\n" f x;;

let dchar b f x = bprintf b "  fprintf(f,\"%%c\",%a);\n" f x;;

let dinthex b f x = bprintf b "  fprintf(f,\"%%x\",%a);\n" f x;;

let dintdec b f x = bprintf b "  fprintf(f,\"%%d\",%a);\n" f x;;

let param s b x = bprintf b "instr->args.%s.%s" (union_id x) s;;

let mode b x = bprintf b "  slv6_print_mode(f,%a);\n" (param "mode") x;;

let printer b (x: xprog) =
  let _token b = function
    | Const s -> string b s
    | Param p -> (
        match p with
            (* registers *)
          | "Rd" | "Rn" | "Rs" | "Rm" | "RdLo" | "RdHi" ->
              let p' = String.sub p 1 (String.length p - 1)
              in bprintf b "  slv6_print_reg(f,%a);\n" (param p') x
          | "CRd" | "CRn" | "CRm" -> string b "CR"; dintdec b (param p) x
              (* REMARK: some examples if the manual use "c" instead of "CR" *)

              (* immediate values *)
          | "immed_16" | "immed_24" | "offset_12" | "offset_8"
          | "immed_3" | "immed_8" | "immed_7" | "immed_5" -> dinthex b (param p) x
          | "opcode_1" | "opcode_2" | "opcode" | "shift_imm" -> dintdec b (param p) x

              (* special cases *)
          | "target_address" when x.xprog.fkind = ARM -> (* B, BL *)
              string b "PC+#"; dinthex b (param "pc_offset") x (* CHECK ME *)
          | "target_addr" when x.xprog.fkind = ARM -> (* BLX(1) *)
              string b "PC+#"; dinthex b (param "pc_offset_h") x (* CHECK ME *)
          | "target_address" when x.xprog.finstr = "Tb_B1" ->
              string b "PC+#"; dinthex b (param "simmed_8_ext") x (* CHECK ME *)
          | "target_address" when x.xprog.finstr = "Tb_B2" ->
              string b "PC+#"; dinthex b (param "simmed_11_ext") x (* CHECK ME *)
          | "target_addr" -> (* Thumb BL, BLX(1) *)
              raise (Failure "Thumb BL, BLX(1) requires a special function")
          | "coproc" -> string b "p"; dintdec b (param p) x
          | "effect" -> (* CPS x2 *)
              let (y, z) = match x.xprog.fkind with ARM -> (2,3) | Thumb -> (0,1) in
                bprintf b "  if (%a==%d) fprintf(f,\"IE\");\n" (param "imod") x y;
                bprintf b "  else if (%a==%d) fprintf(f,\"ID\");\n" (param "imod") x z;
          | "iflags" -> (* CPS x2 *)
              bprintf b "  if (%a) fputc('a',f);\n" (param "A") x;
              bprintf b "  if (%a) fputc('i',f);\n" (param "I") x;
              bprintf b "  if (%a) fputc('f',f);\n" (param "F") x
          | "mode" -> (* CPS, SRS *) mode b x
          | "registers" | "registers_without_pc" | "registers_and_pc" -> (* LSM *)
              bprintf b "  slv6_print_reglist(f,%a);\n" (param "register_list") x
                (* CHECK POP and PUSH cases *)
          | "fields" -> (* MSRimm, MSRreg *)
              bprintf b "  if (%a&1) fputc('c',f);\n" (param "fiald_mask") x;
              bprintf b "  if (%a&2) fputc('x',f);\n" (param "field_mask") x;
              bprintf b "  if (%a&4) fputc('s',f);\n" (param "field_mask") x;
              bprintf b "  if (%a&8) fputc('f',f);\n" (param "field_mask") x;
          | "endian_specifier" -> (* SETEND *)
              let aux b x = bprintf b "%a ? \"BE\" : \"LE32\"" (param "E") x
              in dstring b aux x
          | "x" | "y" -> (* SMLA<x><y>, SMLAL<x><y>, ... *)
              let aux b x = bprintf b "%a ? 'T' : 'B'" (param p) x in dchar b aux x
          | "immed" -> (* SSAT, SSAT16 *) dintdec b (param "sat_imm") x
          | "immediate" -> (* *_M1_Imm *) dinthex b (param "immed_rotated") x
          | "option" -> string b "{"; dinthex b (param p) x; string b "}"
          | "cond" -> bprintf b "  slv6_print_cond(f,%a);\n" (param "cond") x

          | _ -> (* Nothing should remain *)
              raise (Failure ("Printing Param: "^p)))

    | OptParam (p, None) -> (
        match p with
          | "S" | "L" | "X" | "R" ->
              bprintf b "  if (%a) fputc('%c',f);\n" (param p) x p.[0]
          | "!" -> bprintf b "  if (%a) fputc('!',f);\n" (param "W") x

          | _ ->  (* Nothing should remain *)
              raise (Failure ("Printing Opt: "^p)))

    | OptParam (s, Some p) -> (
        match p with
          | "cond" -> bprintf b "  if (%a!=SLV6_AL) slv6_print_cond(f,%a);\n"
              (param "cond") x (param "cond") x
          | "mode" -> (* CPS *)
              bprintf b "  if (%a) {\n  " (param "mmod") x;
              string b s; bprintf b "  "; mode b x; bprintf b "  }\n"
          | "opcode_2" ->
               bprintf b "  if (%a) fprintf(f,\"%%d\",%a);\n" (param p) x (param p) x
          | "shift_imm" when x.xprog.finstr = "PKHBT" ->
              bprintf b "  if (%a) {\n  " (param "shift_imm") x; string b s;
              bprintf b "  "; dintdec b (param "shift_imm") x; bprintf b "  }\n"
          | "shift_imm" when x.xprog.finstr = "PKHTB" ->
              let aux b x = bprintf b "%a ? %a : 32"
                (param "shift_imm") x (param "shift_imm") x
              in string b s; dintdec b aux x
          | "shift" -> (* SSAT, USAT *)
              bprintf b "  if (%a) {\n  " (param "sh") x;
              string b s; bprintf b "  "; string b "  ASR #"; bprintf b "  ";
              ( let aux b x = bprintf b "%a ? %a : 32"
                  (param "shift_imm") x (param "shift_imm") x in dintdec b aux x);
              bprintf b "  } else if (%a) {\n  " (param "shift_imm") x;
              string b s; bprintf b "  "; string b "  LSL #"; bprintf b "  ";
              dintdec b (param "shift_imm") x; bprintf b "  }\n"
          | "rotation" -> (* SXT*, UXT* *)     
              bprintf b "  if (%a) {\n  " (param "rotate") x; string b (s^"ROR #");
              bprintf b "    fprintf(f,\"%%d\",8*%a);\n  }\n" (param "rotate") x;

          | _ -> (* Nothing should remain *)
              raise (Failure ("Printing OptParam: "^p)))

    | PlusMinus -> 
        let aux b x = bprintf b "%a ? '+' : '-'" (param "U") x in dchar b aux x
  in
    bprintf b "void slv6_P_%s(FILE *f, struct SLv6_Instruction *instr) {\n"
      x.xprog.fid;
    bprintf b "  TODO(\"ASM printing of %s\");\n}\n" x.xprog.fid;;
(*     if x.xprog.finstr = "Tb_BL" then ( *)
(*       bprintf b "void slv6_P_%s(FILE *f, struct SLv6_Instruction *instr) {\n" *)
(*         x.xprog.fid; *)
(*       bprintf b "  TODO(\"ASM printing of Thumb BL, BLX(1)\");\n}\n" *)
(*     ) else *)
(*       match x.xprog.fsyntax with *)
(*         | [] -> *)
(*             raise (Invalid_argument ("printer: empty variant list for instruction: "^ *)
(*                      x.xprog.finstr)) *)
(*         | [v] ->  *)
(*             bprintf b "void slv6_P_%s(FILE *f, struct SLv6_Instruction *instr) {\n%a}\n" *)
(*               x.xprog.fid (list "" token) v *)
(*         | _ ->  *)
(*             bprintf b "void slv6_P_%s(FILE *f, struct SLv6_Instruction *instr) {\n%a}\n" *)
(*               x.xprog.fid (list "" token)  *)
(*               (List.hd x.xprog.fsyntax);; (\* FIXME: add variant selection *\) *)

let printers bn xs =
  ( let bh = Buffer.create 10000 in
      bprintf bh "#ifndef %s_PRINTERS_H\n#define %s_PRINTERS_H\n\n" bn bn;
      bprintf bh "#include <stdio.h>\n#include \"%s.h\"\n\n" bn;
      bprintf bh "typedef void (*PrintFunction)(FILE*, struct SLv6_Instruction*);\n";
      bprintf bh "extern PrintFunction slv6_printers[SLV6_TABLE_SIZE];\n\n";
      bprintf bh "extern void slv6_print_instr(FILE*, struct SLv6_Instruction*);\n\n";
      bprintf bh "#endif /* %s_PRINTERS_H */\n" bn;
      let outh = open_out (bn^"_printers.h") in
        Buffer.output_buffer outh bh; close_out outh
  );
  ( let bc = Buffer.create 10000
    and aux b x = bprintf b "\n  slv6_P_%s" x.xprog.fid in
      bprintf bc "#include \"%s_printers.h\"\n#include \"slv6_processor.h\"\n\n" bn;
      bprintf bc "%a\n" (list "\n" printer) xs;
      bprintf bc "PrintFunction slv6_printers[SLV6_TABLE_SIZE] = {%a};\n\n"
        (list "," aux) xs;
      bprintf bc "void slv6_print_instr(FILE *f, struct SLv6_Instruction *instr) {\n";
      bprintf bc "  assert(instr->args.g0.id<SLV6_TABLE_SIZE);\n";
      bprintf bc "  slv6_printers[instr->args.g0.id](f,instr);\n}\n";
      let outc = open_out (bn^"_printers.c") in
        Buffer.output_buffer outc bc; close_out outc
  );;
