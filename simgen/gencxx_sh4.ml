(**
SimSoC-Cert, a toolkit for generating certified processor simulators
See the COPYRIGHTS and LICENSE files.

   C code generator for SH4 processor instructions.
*)

open Ast;;
open Printf;;
open Util;;
open Dec;;
open Dec.Sh4;;

let num = string;;

let hex_of_bin = function
  | "0b00" | "0b0" -> "0"
  | "0b01" | "0b1" -> "1"
  | "0b10" -> "2"
  | "0b11" -> "3"
  | "0b10111" -> "abt"
  | "0b10011" -> "svc"

  | "0" -> "0"
  | "1" -> "1"
  | s -> sprintf "TODO_hex_of_bin /* %s */" s;;

(** C types of usual variables *)

let type_of_var = function

  | "S" | "L" | "mmod" | "F" | "I" | "A" | "R" | "x" | "y" | "X" | "U" | "W"
  | "shifter_carry_out" | "E" -> "bool"

  | "n" | "d" | "m" | "s" | "dHi" | "dLo" | "imod" | "immed_8" | "rotate_imm"
  | "field_mask" | "shift_imm" | "sat_imm" | "rotate" | "cp_num"
  | "immedH" | "immedL" | "offset_8" | "shift" 
  | "opcode_1" | "opcode_2" | "CRn" | "CRm" -> "uint8_t"

  | "cond" -> "SLv6_Condition"
  | "old_mode" | "mode" -> "SLv6_Mode"
  | "accvalue" | "result" | "value" -> "uint64"
  | _ -> "uint32_t";;

(** List the variables of a prog *)

module G = struct

  type typ = string;;

  let global_type = type_of_var;;

  let type_of_size = function
    | Byte -> "uint8_t"
    | Half -> "uint16_t"
    | Word -> "uint32_t";;

  let local_type s e =
    match e with
      | Memory (_, n) -> type_of_size n
      | _ -> type_of_var s;;

  let explicit_annot_type ty _ = match ty with
    | Tint -> "int"
    | Tlong -> "long"
    | Tfloat -> "float"
    | Tdouble -> "double"
    | Tvoid -> "void"
    | Tchar -> "char"
    | Tbool -> "_Bool"
    | Tunsigned -> "unsigned"
    | Tunsigned_long -> "unsigned long"
    | Tunsigned_char -> "unsigned char"
    | Tunsigned_short -> "unsigned short"
    | Tunsigned_int -> "unsigned int"
  
  let case_type = "uint8_t";;

end;;

module V = Ast.Make(G);;

(** extended program type allowing to store extra information *)

type xprog = {
  xprog: prog;
  xid: string; (* the identifier used in the generated code *)
  xgs: (string * string) list; (* "global" variables *)
  xls: (string * string) list; (* local variables *)
  xdec: Codetype.pos_contents array; (* coding table *)
  xvc: exp option; (* validity contraints *)
  xmode: int option; (* mode used by the instruction *)
}

(* merge pseudo-code information with decoding information *)
let xprog_of p (_, pcs) =
  let gs, ls = V.vars p.pinst and id = Flatten.str_ident p in
    {xprog = p; xid = id; xgs = gs; xls = ls; xdec = pcs;
     xvc = None;
     xmode = addr_mode_of_prog p gs};;

let mode_outputs: ((string * string) list) array = Array.create 5 [];;

(** Heuristic to chose between signed and unsigned; true means signed *)

(** Add a cast to a signed type *)
let rec to_signed e = match e with
  | Fun ("to_u64", [e']) -> Fun ("to_u64", [to_signed e'])
  | e' -> Fun ("to_signed", [e']);;

(** Generate the code corresponding to an expression *)

let func = function
  | "not" -> "!"
  | "NOT" -> "~"
  | "GE" -> "get_GE"
  | "TLB" -> "slv6_TLB"
  | "opp" -> "-"
  | s -> s;;

let implicit_arg = function
  | "ConditionPassed" -> "&proc->cpsr, "
  | "write_word" | "write_half" | "write_byte" -> "proc->mmu_ptr, "
  | "CP15_reg1_EEbit" | "CP15_reg1_Ubit" | "CP15_reg1_Vbit" -> "&proc->cp15"
  | "set_bit" | "set_field" -> "addr_of_"
  | "InAPrivilegedMode" | "CurrentModeHasSPSR" | "address_of_next_instruction"
  | "address_of_current_instruction" | "high_vectors_configured" -> "proc"
  | "set_reg_m" -> "proc, "
  | _ -> "";;

let mode m = Genpc.string_of_mode m;;

let binop = function
  | "and" -> "&&"
  | "or" -> "||"
  | "AND" -> "&"
  | "OR" | "|" -> "|"
  | "EOR" -> "^"
  | "Logical_Shift_Left" -> "<<"
  | "Logical_Shift_Right" -> ">>"
  | "==" -> "=="
  | "!=" -> "!="
  | ">=" -> ">="
  | "<" -> "<"
  | "+" -> "+"
  | "-" -> "-"
  | "<<" -> "<<"
  | "*" -> "*"
  | "Rotate_Right" -> "rotate_right"
  | "Arithmetic_Shift_Right" -> "asr"

  | "zgt" -> ">"
  | s -> sprintf "TODO_binop /* %s */" s;;

let binop_64 = function
  | "Logical_Shift_Left" -> "I64_lsl"
  | "-" -> "I64_sub"
  | "+" -> "I64_add"
  | "OR" -> "I64_or"
  | _ -> "TODO_binop64"

let reg_id = function
  | "15" -> "PC"
  | "14" -> "LR"
  | "13" -> "SP"
  | n -> n;;

let cpsr_flag = function
  | "31" -> "N_flag"
  | "30" -> "Z_flag"
  | "29" -> "C_flag"
  | "28" -> "V_flag"
  | "27" -> "Q_flag"
  | "24" -> "J_flag"
  | "19" -> "GE3"
  | "18" -> "GE2"
  | "17" -> "GE1"
  | "16" -> "GE0"
  | "9" -> "E_flag"
  | "8" -> "A_flag"
  | "7" -> "I_flag"
  | "6" -> "F_flag"
  | "5" -> "T_flag"
  | s -> "TODO_cpsr_flag_"^s;;

let cpsr_field = function
  | "4", "0" -> "mode"
  | s1, s2 -> "TODO_cpsr_field_"^s1^"_"^s2;;

let access_type = function
  | Byte -> "byte"
  | Half -> "half"
  | Word -> "word";;

let optemps = ["index"; "offset_8"; "end_address"];;

let input_registers = [];;

let is_pointer p s = match p.xprog.pkind with
  | InstARM | InstThumb -> false
  | Mode n -> List.mem s (List.map fst (mode_outputs.(n-1)));;

let typeof x v =
  try List.assoc v x.xgs
  with Not_found -> List.assoc v x.xls;;

let not_cast_to_int64 p = 
  List.mem p.xid [ "DMULS" 
                 ; "DMULU"
                 ; "MACL_"
                 ; "MACW"
                 ; "MULL"
                 ; "MULS"
                 ; "MULU" ]
let is_int64, bprintf64 = 
  let r = ref false in
  (fun () -> !r), 
  fun b f1 f_rec f2 -> 
    begin
      f1 b;
      r := true;
      f_rec b;
      r := false;
      f2 b;
    end

let add_proc_param f = 
  match Str.str_match "\\(.+\\)_\\(.+\\)" f [ 1 ; 2 ] with
    | Some [ s1 ; s2 ] when List.mem s1 [ "Delay" ; "Write" ; "Read" ] && List.mem s2 [ "Slot" ; "Byte" ; "Word" ; "Long" ] -> 
      "proc, "
    | _ -> ""

let rec exp p b = 
  let to_iu64 = 
    let to_iu = if p.xid.[0] = 'S' then "to_i64" else "to_u64" in
    fun b -> bprintf b "%s(%a)" to_iu in
  let iu64 = if is_int64 () then to_iu64 else fun b -> bprintf b "%a" in
  function
  | Bin s -> string b (hex_of_bin s)
  | Hex s | Num s -> iu64 b string s
  | If_exp (e1, e2, e3) -> bprintf b "(%a? %a: %a)" (exp p) e1 (exp p) e2 (exp p) e3
  | BinOp (e1, ("Rotate_Right"|"Arithmetic_Shift_Right" as op), e2) ->
      (exp p) b (Fun (binop op, [e1; e2]))
  | BinOp (e, "<<", Num "32") ->
      bprintf b "I64_lsl(%a, 32)" (exp p) e
  | BinOp (BinOp (Var "operand1", "*", Var "operand2"), "<", Num "0") -> 
    bprintf b "I64_compare(I64_mul(to_i64(operand1), to_i64(operand2)), to_i64(0)) < 0"
  (*| BinOp (e, ("<"|">=" as op), Num "0") -> bprintf b "(%a %s 0)" (exp p) (to_signed e) op*)
  | BinOp (Num n, "*", e) | BinOp (e, "*", Num n)->
      bprintf b "(%a * %s)" (exp p) e n
  | BinOp (e1, "*", e2) -> 
    if not_cast_to_int64 p then
      bprintf b "%a * %a" (exp p) e1 (exp p) e2
    else
      bprintf b "I64_mul(%a, %a)" (exp p) e1 (exp p) e2
  | BinOp (e1, op, e2) -> 
    if is_int64 () then
      if op = "==" then
        bprintf b "I64_ucompare(%a, %a) == 0" (exp p) e1 (exp p) e2
      else
        bprintf b "%s(%a, %a)" (binop_64 op) (exp p) e1 (exp p) e2
    else
      bprintf b "(%a %s %a)" (exp p) e1 (binop op) (exp p) e2

  (* try to find the right conversion operator *)
  | Fun ("to_signed", [Var v]) when typeof p v = "uint32_t" ->
      bprintf b "to_int32(%s)" v
  | Fun (f, es) -> 
    let implicit_arg f = add_proc_param f ^ implicit_arg f in
    if is_int64 () then
      to_iu64 b (fun b () -> bprintf b "%s(%s%a)"
        (func f) (implicit_arg f) (list_sep ", " (fun b s -> if s = Var "shift_imm" then exp p b s else begin bprintf b "I64_to_int32(" ; exp p b s ; bprintf b ")" end)) es) ()
    else if f = "SignedSat" || f = "SignedDoesSat" then
      (* extra coercion to the 1st parameter *)
      let e, es = match es with [] -> assert false | e :: es -> e, es in
      bprintf b "%s(%s%a,%a)"
        (func f) (implicit_arg f) 
        (fun b s -> begin bprintf b "I64_of_int32(" ; exp p b s ; bprintf b ")" end) 
        e (list_sep ", " (exp p)) es
    else
      bprintf b "%s(%s%a)"
        (func f) (implicit_arg f) (list_sep ", " (exp p)) es
  | CPSR -> string b "StatusRegister_to_uint32(&proc->cpsr)"
  | SPSR None -> string b "StatusRegister_to_uint32(spsr(proc))"
  | SPSR (Some m) -> bprintf b "StatusRegister_to_uint32(spsr_m(proc,%s))" (mode m)
  | Reg (Var ( "SPC" | "GBR" | "VBR" | "SGR" | "DBR" | "MACH" | "MACL" | "PR" 
             | "EXPEVT" | "FPUL" | "FPSCR" | "TRA" as s), None) -> bprintf b "proc->%s" s
  | Reg (Var "SR", None) -> bprintf b "reg_sr(proc)"
  | Reg (Var "SSR", None) -> bprintf b "reg_ssr(proc)"
  | Reg (Var s, None) ->
    iu64 b 
      (if List.mem s input_registers then 
         fun b -> bprintf b "old_R%s"
       else if Str.l_match [Str.regexp "R._BANK", s] then
         fun b s -> bprintf b "reg_bank(proc,%c)" s.[1]
       else
         fun b -> bprintf b "reg(proc,%s)") s
  | Reg (Num "15", None) -> bprintf b "proc->pc"
  | Reg (e, None) -> bprintf b "reg(proc,%a)" (exp p) e
  | Reg (e, Some m) -> bprintf b "reg_m(proc,%a,%s)" (exp p) e (mode m)
  | Var s -> if is_pointer p s then bprintf b "*%s" s else 
      if is_int64 () && type_of_var s <> "uint64" && s <> "shift_imm" then 
        to_iu64 b string s
      else string b s 
  | Memory (e, n) -> bprintf b "read_%s(proc->mmu_ptr,%a)" (access_type n) (exp p) e
  | Range (CPSR, Flag (s,_)) -> bprintf b "proc->SR.%s" s
  | Range (e1, Index e2) -> bprintf b "get_bit(%a,%a)" (exp p) e1 (exp p) e2
  | Range (e, Bits (n1, n2)) ->
      begin
        let signed =
          if p.xid.[0] = 'S' || p.xid.[0] = 'Q' then "_signed" else ""
        in
          match n1, n2 with
            | "15", "0" -> bprintf b "get%s_half_0(%a)" signed (exp p) e
            | "31", "16" -> bprintf b "get%s_half_1(%a)" signed (exp p) e
            | "7", "0" -> bprintf b "get%s_byte_0(%a)" signed (exp p) e
            | "15", "8" -> bprintf b "get%s_byte_1(%a)" signed (exp p) e
            | "23", "16" -> bprintf b "get%s_byte_2(%a)" signed (exp p) e
            | "31", "24" -> bprintf b "get%s_byte_3(%a)" signed (exp p) e
            | "31", "0" 
            | "63", "32"
            | "47", "16" -> 
              bprintf64 b 
                (fun b -> bprintf b "get_bits64(") 
                (fun b -> exp p b e)
                (fun b -> bprintf b ",%s,%s)" n1 n2)
            | _ -> bprintf b "get_bits(%a,%s,%s)" (exp p) e n1 n2
      end
  | Coproc_exp (e, f, es) ->
      bprintf b "%s(proc,%a)" (func f) (list_sep "," (exp p)) (e::es)
  | _ -> string b "TODO(\"exp\")";;

(** Generate the body of an instruction function *)

let rec inst p k b = function
  | Block _ | For _ | While _ | If _ | Case _ as i ->
      bprintf b "%a%a" indent k (inst_aux p k) i
  | i -> bprintf b "%a%a;" indent k (inst_aux p k) i

and inst_aux p k b = function
  | Unpredictable -> string b "unpredictable()"
  | Assign (Var "value", If_exp (BinOp (Var "R", "==", Num "1"), e1, e2)) -> 
    (* CompCert does not handle an affectation containing such a value, we rewrite to an semantically equivalent one. For an example, see "SMMUL". *)
    inst_aux p k b (If (BinOp (Var "R", "==", Num "1"), Assign (Var "value", e1), Some (Assign (Var "value", e2))))
  | Assign (dst, src) -> affect p k b dst src
  | Proc (f, es) -> bprintf b "%s(%s%s%a)" f (add_proc_param f) (implicit_arg f) (list_sep ", " (exp p)) es
  | Assert e -> bprintf b "assert(%a)" (exp p) e
  | Coproc (e, f, es) ->
      bprintf b "%s(proc,%a)" (func f) (list_sep "," (exp p)) (e::es)

  | Block [] -> ()
  | Block (Block _ | For _ | While _ | If _ | Case _ as i :: is) ->
      bprintf b "%a\n%a" (inst_aux p k) i (list_sep "\n" (inst p k)) is
  | Block (i :: is) ->
      bprintf b "%a;\n%a" (inst_aux p k) i (list_sep "\n" (inst p k)) is

  | Let (_, _, is, _) ->
      bprintf b "%a%a" 
        indent k   (list (inst p (k+2))) is

  | While (e, i) -> bprintf b "while (%a)\n%a" (exp p) e (inst p (k+2)) i

  | For (counter, min, max, i) ->
      bprintf b "size_t %s; for (%s = %a; %s<=%a; ++%s) {\n%a\n}"
        counter counter num min counter num max counter (inst p (k+2)) i

  | Case (e, s, o) ->
      bprintf b "switch (%a) {\n%a%a  default:\n%a\n  }"
        (exp p) e (list (case_aux p k)) s indent k
        (fun b -> function
          | None -> bprintf b "%aabort();" indent (k+2)
          | Some i -> inst p (k+2) b i) o

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
  | Return e -> bprintf b "return %a;\n" (exp p) e

and case_aux p k b (n, i) =
  bprintf b "%acase %s:\n%a\n%abreak;\n"
    indent k (hex_of_bin n) (inst p (k+2)) i indent (k+2)

and affect p k b dst src =
  if src = Unpredictable_exp then string b "unpredictable()"
  else match dst with
    | Reg (Var "d", _) -> bprintf b
        "set_reg_or_pc(proc,d,%a)" (exp p) src
    | Reg (Var s, None) when Str.l_match [Str.regexp "R._BANK", s] -> bprintf b "set_reg_bank(proc,%c,%a)" s.[1] (exp p) src
    | Reg (Var ( "SPC" | "GBR" | "VBR" | "SGR" | "DBR" | "MACH" | "MACL" | "PR" 
               | "EXPEVT" | "FPUL" | "FPSCR" | "TRA" as s), None) -> bprintf b "proc->%s = %a" s (exp p) src
    | Reg (Var "SR", None) -> bprintf b "set_reg_sr(proc, %a)" (exp p) src
    | Reg (Var "SSR", None) -> bprintf b "set_reg_ssr(proc, %a)" (exp p) src
    | Reg (Num "15", None) -> bprintf b "set_pc_raw(proc,%a)" (exp p) src
    | Reg (e, None) -> bprintf b "set_reg(proc,%a,%a)" (exp p) e (exp p) src
    | Reg (e, Some m) ->
        bprintf b "set_reg_m(proc,%a,%s,%a)" (exp p) e (mode m) (exp p) src
    | CPSR -> (
        match src with
          | SPSR None -> bprintf b "copy_StatusRegister(&proc->cpsr, spsr(proc))"
          | SPSR (Some m) ->
              bprintf b "copy_StatusRegister(&proc->cpsr, spsr_m(proc,%s))" (mode m)
          | _ -> bprintf b "set_StatusRegister(&proc->cpsr,%a)" (exp p) src)
    | SPSR None -> (
        match src with
          | CPSR -> bprintf b "copy_StatusRegister(spsr(proc), &proc->cpsr)"
          | _ -> bprintf b "set_StatusRegister(spsr(proc),%a)" (exp p) src)
    | SPSR (Some m) -> (
        match src with
          | CPSR -> bprintf b "copy_StatusRegister(spsr_m(proc,%s), &proc->cpsr)" (mode m)
          | _ -> bprintf b "set_StatusRegister(spsr_m(proc,%s),%a)" (mode m) (exp p) src)
    | Var (("accvalue" | "result") as v)
    | Var ("value" as v) when p.xid.[0] = 'S' || p.xid = "UMAAL" -> 
      bprintf64 b (fun b -> bprintf b "%a = " (exp p) (Var v)) (fun b -> exp p b src) (fun _ -> ())
    | Var v -> bprintf b "%a = %a" (exp p) (Var v) (exp p) src
    | Range (CPSR, Flag (s,_)) ->
        bprintf b "proc->SR.%s = %a" s (exp p) src
    | Range (e1, Bits (n1, n2)) ->
        inst_aux p k b (Proc ("set_field", [e1; Num n1; Num n2; src]))
    | Memory (addr, n) ->
        inst_aux p k b (Proc ("write_" ^ access_type n, [addr; src]))
    | Range (e, Index n) -> inst_aux p k b (Proc ("set_bit", [e; n; src]))
    | _ -> string b "TODO(\"affect\")";;

(** Generate a function modeling an instruction of the processor *)

let prog_var b s = bprintf b "<%s>" s;;

let prog_arg b (v,t) = bprintf b ",\n    const %s %s" t v;;

let prog_out b (v,t) = bprintf b ",\n    %s *%s" t v;;

let local_decl b (v,t) = bprintf b "  %s %s;\n" t v;;

let inreg_load b s =
  bprintf b "  const uint32_t old_R%s = reg(proc,%s);\n" s s;;

let comment b p = bprintf b "/* %a */\n" Genpc.name p.xprog;;

let arg_sep l l' = match l, l' with _::_, _::_ -> ",\n    " | _ -> "";;

let print_first b (s, _) = string b s;;

(* Defintion of the functions. This should be printed in a source file (.c) *)
let prog b p =
  let ss = List.fold_left (fun l (s, _) -> s::l) [] p.xgs in
  let inregs = List.filter (fun x -> List.mem x input_registers) ss in
    match p.xprog.pkind with
      | InstARM ->
          bprintf b "%avoid %s(struct SLSH4_Processor *proc%a)\n{\n%a%a%a\n}\n" comment p
            p.xid
            (list prog_arg) p.xgs
            (list inreg_load) inregs
            (list local_decl) p.xls
            (inst p 2) p.xprog.pinst
      | InstThumb -> () (* TODO: thumb mode *)
      | Mode m ->
          let os = mode_outputs.(m-1)
          and ls' = List.filter (fun (x, _) -> List.mem x optemps) p.xls in
            bprintf b "%avoid %s(struct SLSH4_Processor *proc%a%a)\n{\n%a%a%a\n}\n" comment p
              p.xid
              (list prog_arg) p.xgs
              (list prog_out) os
              (list inreg_load) inregs
              (list local_decl) ls'
              (inst p 2) p.xprog.pinst;;

(* Declaration of the functions. This should be printed in a header file (.h) *)
let decl b p =
  match p.xprog.pkind with
    | InstARM  ->
        bprintf b "%aextern void %s(struct SLSH4_Processor*%a);\nextern bool try_%s(struct SLSH4_Processor*, uint16_t bincode);\n"
          comment p p.xid
          (list prog_arg) p.xgs p.xid
    | InstThumb -> () (* TODO: thumb mode *)
    | Mode _ -> assert false

(* For some LSM instructions, the operand has side effects that must be executed
 * after the instruction itself *)
let lsm_hack p =
  let rec inst = function
    | Block is -> Block (List.map inst is)
    | If (_, Assign (Reg (Var "n", None), e), None) -> Assign (Var "new_Rn", e)
    | i -> i
  in
  let guard_ldm_stm i = (i.iname = "LDM" || i.iname = "STM") && i.ivariant <> Some "2"
  in let a = If (Var "W",
                 Assign (Reg (Var "n", None), Var "new_Rn"),
                 None)
  in match p.pkind with
    | InstARM when guard_ldm_stm p.pident ->
        (* add 'if (W) then Rn = new_Rn' at the end of the main 'if' *)
        let i = match p.pinst with
          | If (c, Block (i1::i2::tl), None) -> If (c, Block (i1::i2::a::tl), None)
          | Block ([x; If (c, Block (i1::i2::tl), None)]) ->
              Block ([x; If (c, Block (i1::i2::a::tl), None)])
          | _ -> raise (Failure ("Unexpected AST shape: " ^ p.pident.iname))
        in { p with pinst = i }
    | InstARM when p.pident.iname = "RFE" ->
        (* add 'if (W) then Rn = new_Rn' at the end of the main block *)
        let i = match p.pinst with
          | Block (l) -> Block (a::l)
          | _ -> raise (Failure ("Unexpected AST shape: " ^ p.pident.iname))
        in { p with pinst = i }
    | InstARM when p.pident.iname = "SRS" ->
        (* add 'if (W) then R13_mode = new_Rn' at the end of the main block *)
        let a' = If (Var "W",
                     Proc("set_reg_m", [Num "13"; Var "mode"; Var "new_Rn"]),
                     None) in
        let i = match p.pinst with
          | Block (l) -> Block (l @ [a'])
          | _ -> raise (Failure ("Unexpected AST shape: " ^ p.pident.iname))
        in { p with pinst = i }
    | Mode 4 ->
        (* replace 'If (...) then Rn = ...' by 'new_Rn = ...' *)
        { p with pinst = inst p.pinst }
    | _ -> p;;

(* Split the list of programs according to their kind *)
let split xs =
  let is = ref [] and ms = Array.create 5 [] in
  let rec aux l =
    match l with
      | x :: tl -> (
          match x.xprog.pkind with
            | Mode i -> ms.(i-1) <- x::ms.(i-1)
            | InstARM  -> is := x::!is
            | InstThumb -> ()); (* TODO: Thumb mode *)
          aux tl
      | [] -> (!is, ms)
  in aux xs;;

(* get the list of parameters *)
let parameters_of pca : (string * int * int) list =
  let rename s =
    if s.[0] = 'R'
    then String.sub s 1 (String.length s -1)
    else match s with
      | "sh" -> "shift" (* work-around for specification erratum *)
      | "ImmedL" -> "immedL" (* work-around for specification erratum *)
      | _ -> s
  in
  let aux (n, l) pc = match pc with
    | Codetype.Param1 c -> (n+1, (String.make 1 c, n, n) :: l)
    | Codetype.Param1s s-> (n+1, (rename s, n, n) :: l)
    | Codetype.Range (s, size, _) ->
        let s' = rename s in
        let e = s', n+size-1, n in
          (n+1, (
             match l with (* avoid duplicates *)
               | (x, _, _) :: _ -> if x = s' then l else e :: l
               | [] -> [e]
           ))
    | _ -> (n+1, l)
  in
  let _, ps = Array.fold_left aux (0, []) pca in ps;;

(* generate the code extracing the parameters from the instruction code *)
let dec_param gs vc buf (s, a, b) =
  (* exclude "shifter_operand" *)
  if (s, a, b) = ("shifter_operand", 11, 0) then ()
  else
    (* compute the list of used parameters *)
    let gs' = ["H1", "uint8_t"; "H2", "uint8_t"] @ match vc with
      | Some e ->
          let vs, _ = V.vars_exp (StrMap.empty, StrMap.empty) e in
            list_of_map vs @ gs
      | None -> gs
    in try
        let t = List.assoc s gs' in
          if s = "cond" then (
            (* special case for cond, because decoding of this field can fail *)
            bprintf buf "  const uint32_t cond_tmp = get_bits(bincode,%d,%d);\n" a b;
            bprintf buf "  if (cond_tmp>14) return false;\n";
            bprintf buf "  const SLSH4_Condition cond =\n";
            bprintf buf "    ((SLSH4_Condition) cond_tmp);\n"
          ) else if (s, a, b) = ("mode", 4, 0) then (
            (* special case for mode, because decoding of this field can fail *)
            bprintf buf "  const uint32_t mode_tmp = get_bits(bincode,4,0);\n";
            bprintf buf "  SLSH4_Mode mode;\n";
            bprintf buf
              "  if (!decode_mode(&mode,bincode)) return false;\n"
          ) else
            if a = b then
              bprintf buf "  %s %s = get_bit(bincode,%d);\n" t s a
            else
              bprintf buf "  %s %s = get_bits(bincode,%d,%d);\n" t s a b
      with Not_found -> ();; (* do not extract unused parameters *)

(* compute the mask and the value corresponding to a coding table *)
let mask_value pcs =
  let f pc (m,v) =
    let m' = Int32.shift_left m 1 and v' = Int32.shift_left v 1 in
      match pc with
          (* FIXME: we should distinguish between UNDEFINED and
           * UNPREDICTABLE *)
        | Codetype.Value true | Codetype.Shouldbe true ->
            (Int32.succ m', Int32.succ v')
        | Codetype.Value false | Codetype.Shouldbe false ->
            (Int32.succ m', v')
        | _ -> (m', v')
    in Array.fold_right f pcs (Int32.zero, Int32.zero);;

(* generate the decoder - instructions *)
let dec_inst b is =
  (* Phase A: check bits fixed by the coding table *)
  let instA b p =
    let (mask, value) = mask_value p.xdec in
      bprintf b "  if ((bincode&0x%08lx)==0x%08lx && try_%s(proc,bincode)) {\n"
        mask value p.xid;
      bprintf b "    DEBUG(puts(\"decoder choice: %s\"));\n" p.xid;
      bprintf b "    assert(!found); found = true;\n  }\n\n"
  in
    (* Phase B: extract parameters and check validity *)
  let instB b p =
    bprintf b "bool try_%s(struct SLSH4_Processor *proc, uint16_t bincode) {\n" p.xid;

    (* extract parameters *)
    bprintf b "%a" (list (dec_param p.xgs p.xvc)) (parameters_of p.xdec);
    (* check validity *)
    (match p.xvc with
       | Some e -> bprintf b "  if (!(%a)) return false;\n" (exp p) e
       | None -> ());
    (* decode the mode *)
    (match p.xmode with
       | Some m ->
           let os = mode_outputs.(m-1) in
           let aux b (s,_) = bprintf b ",&%s" s in
             bprintf b "%a  if (!try_M%d(proc,bincode%a)) return false;\n"
               (list local_decl) os m (list aux) os
       | None -> ());

    (* execute the instruction *)
    let aux b (s,_) = bprintf b ",%s" s in
    bprintf b "  EXEC(%s(proc%a));\n" p.xid (list aux) p.xgs;
    bprintf b "  return true;\n}\n"
  in
  let is' = List.rev is in
    bprintf b "bool decode_and_exec(struct SLSH4_Processor *proc, uint16_t bincode) {\n";
    bprintf b "  bool found = false;\n\n";
    bprintf b "%a" (list instA) is';
    bprintf b "  return found;\n}\n\n%a"
      (list_sep "\n" instB) is';;

(* declare the try_Mx methods *)
let decl_try b m os =
  bprintf b "\nextern bool try_M%d(struct SLSH4_Processor*, uint32_t bincode%a);\n"
    (m+1) (list prog_out) os;;

(* generate the decoder - modes *)
let dec_modes b ms =
  (* Phase A: check bits fixed by the coding table *)
  let modeA os b p =
    let (mask, value) = mask_value p.xdec in
      bprintf b "  if ((bincode&0x%08lx)==0x%08lx &&\n      try_%s(proc,bincode,%a)) {\n"
        mask value p.xid (list_sep "," print_first) os;
      bprintf b "    assert(!found); found = true;\n  }\n"
  in (* Phase B: extract parameters and check validity *)
  let modeB os b p =
    bprintf b "bool try_%s(struct SLSH4_Processor *proc, uint32_t bincode%a) {\n"
      p.xid (list prog_out) os;
    (* extract parameters *)
    bprintf b "%a" (list (dec_param p.xgs p.xvc)) (parameters_of p.xdec);
    (* check validity *)
    (match p.xvc with
       | Some e -> bprintf b "  if (!(%a)) return false;\n" (exp p) e
       | None -> ());
    (* execute the mode case *)
    bprintf b "  EXEC(%s(proc,%a,%a));\n" p.xid
      (list_sep "," print_first) p.xgs (list_sep "," print_first) os;
    bprintf b "  return true;\n}\n"
  in (* generate the decoder for mode i *)
  let dec_mode b i ms =
    let ms' = List.rev ms in
    let os = mode_outputs.(i) in
      bprintf b "\nbool try_M%d(struct SLSH4_Processor *proc, uint32_t bincode%a) {\n"
        (i+1) (list prog_out) os;
      bprintf b "  bool found = false;\n%a"
        (list (modeA os)) ms';
      bprintf b "  return found;\n}\n\n%a" (list_sep "\n" (modeB os)) ms';
  in Array.iteri (dec_mode b) ms;;

(* main function
 * bn: output file basename, pcs: pseudo-code trees, decs: decoding rules *)
let lib (bn: string) ({ body = pcs ; _ } : program) (decs: Codetype.maplist) =
(*  let pcs_len = List.length pcs and decs_len = List.length decs in *)
  (* remove decoding rules that don't have corresponding pseudo-code trees *)
  let decs' =
    let aux (lh, _) = add_mode lh <> DecEncoding in
      List.filter aux decs in
(*  let decs'_len = List.length decs' in *)
  let xs = List.map2 xprog_of pcs decs' in (* compute extended programs *)
  let is, _ = split xs in (* group by kind *)
(*  let is_len = List.length is and ms_len = Array.length ms in *)
  (* create buffers for header file (bh) and source file (bc) *)
  let bh = Buffer.create 10000 and bc = Buffer.create 10000 in
    (* generate the header file *)
    bprintf bh "#ifndef SH4_ISS_H\n#define SH4_ISS_H\n\n";
    bprintf bh "#include \"slsh4_iss_h_prelude.h\"\n\n";
    bprintf bh "%a" (list_sep "\n" decl) xs;

    bprintf bh "\nextern bool decode_and_exec(struct SLSH4_Processor*, uint16_t bincode);\n";
    bprintf bh "\nEND_SIMSOC_NAMESPACE\n";
    bprintf bh "\n#endif /* SH4_ISS_H */\n";
    (* generate the source file *)
    bprintf bc "#include \"%s.h\"\n#include \"slsh4_iss_c_prelude.h\"\n\n%a\n%a"
      bn (list_sep "\n" prog) xs dec_inst is;
    bprintf bc "\nEND_SIMSOC_NAMESPACE\n";
(**    bprintf bc "bool decode_and_exec(struct SLSH4_Processor *proc, uint16_t bincode) {\n";
    bprintf bc "  bool found = false;\n";
    bprintf bc "# Pseudo-Code Trees: %d\n" pcs_len;
    bprintf bc "# Decoding Rules: %d\n" decs_len;
    bprintf bc "# Decoding Rules (Filtered): %d\n" decs'_len;
    bprintf bc "is_len: %d\n" is_len;
    bprintf bc "ms_len: %d\n" ms_len;
    bprintf bc "  return found;\n}\n"; *)
    (* write buffers to files *)
    let outh = open_out (bn^".h") and outc = open_out (bn^".c") in
      Buffer.output_buffer outh bh; close_out outh;
      Buffer.output_buffer outc bc; close_out outc;;
