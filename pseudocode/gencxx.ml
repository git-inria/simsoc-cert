(**
   SimSoC-Cert, a library on processor architectures for embedded systems.
   See the COPYRIGHTS and LICENSE files.

   Formalization of the ARM architecture version 6 following the:

   ARM Architecture Reference Manual, Issue I, July 2005.

   Page numbers refer to ARMv6.pdf.

   C code generator for simulation (see directory ../cxx)
*)

open Ast;;
open Printf;;
open Util;;
open Dec;;

let num = string;;

let hex_of_bin = function
  | "0b00" | "0b0" -> "0"
  | "0b01" | "0b1" -> "1"
  | "0b10" -> "2"
  | "0b11" -> "3"
  | "0b10111" -> "abt"
  | "0b10011" -> "svc"
  | _ -> "TODO_hex_of_bin";;

(** C types of usual variables *)

let type_of_var = function

  | "S" | "L" | "mmod" | "F" | "I" | "A" | "R" | "x" | "y" | "X" | "U" | "W"
  | "shifter_carry_out" | "E" -> "bool"

  | "n" | "d" | "m" | "s" | "dHi" | "dLo" | "imod" | "immed_8" | "rotate_imm"
  | "field_mask" | "shift_imm" | "sat_imm" | "rotate" | "cp_num"
  | "immedH" | "immedL" | "offset_8" | "shift" -> "uint8_t"

  | "cond" -> "Condition"
  | "mode" -> "Mode"
  | "accvalue" | "result" -> "uint64_t"
  | "processor_id" -> "size_t"
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

let str_ident p =
  let ident b p =
    let i = p.pident in
      match p.pkind with
        | Inst ->
            bprintf b "%s%a%a" i.iname
              (option "" string) i.ivariant (list "" string) i.iparams
        | Mode m ->
            bprintf b "M%d_%s" m i.iname
  in
  let b = Buffer.create 16 in ident b p; Buffer.contents b;;

(* merge pseudo-code information with decoding information *)
let xprog_of p (_, pcs) =
  let gs, ls = V.vars p and id = str_ident p in
    {xprog = p; xid = id; xgs = gs; xls = ls; xdec = pcs;
     xvc = Validity.to_exp id;
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
  | s -> s;;

let implicit_arg = function
  | "ConditionPassed" -> "&proc->cpsr,"
  | "write_word" | "write_half" | "write_byte" -> "&proc->mmu,"
  | "CP15_reg1_EEbit" | "CP15_reg1_Ubit" | "CP15_reg1_Vbit" -> "&proc->cp15"
  | "set_bit" | "set_field" -> "addr_of_"
  | "InAPrivilegedMode" | "CurrentModeHasSPSR" | "address_of_next_instruction"
  | "address_of_current_instruction" | "high_vectors_configured" -> "proc"
  | _ -> "";;

let mode m = Genpc.string_of_mode m;;

let binop = function
  | "and" -> "&&"
  | "or" -> "||"
  | "AND" -> "&"
  | "OR" -> "|"
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
  | _ -> "TODO_binop";;

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

let input_registers = ["n"; "m"; "s"; "dLo"];;

let is_pointer p s = match p.xprog.pkind with
  | Inst -> false
  | Mode n -> List.mem s (List.map fst (mode_outputs.(n-1)));;

let typeof x v =
  try List.assoc v x.xgs
  with Not_found -> List.assoc v x.xls;;

let rec exp p b = function
  | Bin s -> string b (hex_of_bin s)
  | Hex s | Num s -> string b s
  | If_exp (e1, e2, e3) -> bprintf b "(%a? %a: %a)" (exp p) e1 (exp p) e2 (exp p) e3
  | BinOp (e1, ("Rotate_Right"|"Arithmetic_Shift_Right" as op), e2) ->
      (exp p) b (Fun (binop op, [e1; e2]))
  | BinOp (e, "<<", Num "32") ->
      bprintf b "(to_u64(%a) << 32)" (exp p) e
  | BinOp (e, ("<"|">=" as op), Num "0") ->
      bprintf b "(%a %s 0)" (exp p) (to_signed e) op
  | BinOp (e1, "*", e2) -> if p.xid.[0] = 'S'
    then bprintf b "(to_i64(%a) * to_i64(%a))" (exp p) e1 (exp p) e2
    else bprintf b "(to_u64(%a) * to_u64(%a))" (exp p) e1 (exp p) e2
  | BinOp (e1, op, e2) -> bprintf b "(%a %s %a)" (exp p) e1 (binop op) (exp p) e2

  (* try to find the right conversion operator *)
  | Fun ("to_signed", [Var v]) when typeof p v = "uint32_t" ->
      bprintf b "to_int32(%s)" v
  | Fun ("to_signed", [e]) -> bprintf b "to_int64(%a)" (exp p) e

  | Fun (f, es) -> bprintf b "%s(%s%a)"
      (func f) (implicit_arg f) (list ", " (exp p)) es
  | CPSR -> string b "StatusRegister_to_uint32(&proc->cpsr)"
  | SPSR None -> string b "StatusRegister_to_uint32(spsr(proc))"
  | SPSR (Some m) -> bprintf b "StatusRegister_to_uint32(spsr_m(proc,%s))" (mode m)
  | Reg (Var s, None) ->
      if List.mem s input_registers
      then bprintf b "old_R%s" s
      else bprintf b "reg(proc,%s)" s
  | Reg (e, None) -> bprintf b "reg(proc,%a)" (exp p) e
  | Reg (e, Some m) -> bprintf b "reg_m(proc,%a,%s)" (exp p) e (mode m)
  | Var s -> if is_pointer p s then bprintf b "*%s" s else string b s
  | Memory (e, n) -> bprintf b "read_%s(&proc->mmu,%a)" (access_type n) (exp p) e
  | Range (CPSR, Flag (s,_)) -> bprintf b "proc->cpsr.%s_flag" s
  | Range (CPSR, Index (Num s)) -> bprintf b "proc->cpsr.%s" (cpsr_flag s)
  | Range (e1, Index e2) -> bprintf b "get_bit(%a,%a)" (exp p) e1 (exp p) e2
  | Range (e, Bits (n1, n2)) ->
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
      bprintf b "%s(proc,%a)" (func f) (list "," (exp p)) (e::es)
  | _ -> string b "TODO(\"exp\")";;

(** Generate the body of an instruction function *)

let rec inst p k b = function
  | Block _ | For _ | While _ | If _ | Case _ as i ->
      bprintf b "%a%a" indent k (inst_aux p k) i
  | i -> bprintf b "%a%a;" indent k (inst_aux p k) i

and inst_aux p k b = function
  | Unpredictable -> string b "unpredictable()"
  | Affect (dst, src) -> affect p k b dst src
  | Proc (f, es) -> bprintf b "%s(%s%a)" f (implicit_arg f) (list ", " (exp p)) es
  | Assert e -> bprintf b "assert(%a)" (exp p) e
  | Coproc (e, f, es) ->
      bprintf b "%s(proc,%a)" (func f) (list "," (exp p)) (e::es)

  | Block [] -> ()
  | Block (Block _ | For _ | While _ | If _ | Case _ as i :: is) ->
      bprintf b "%a\n%a" (inst_aux p k) i (list "\n" (inst p k)) is
  | Block (i :: is) ->
      bprintf b "%a;\n%a" (inst_aux p k) i (list "\n" (inst p k)) is

  | While (e, i) -> bprintf b "while (%a)\n%a" (exp p) e (inst p (k+2)) i

  | For (counter, min, max, i) ->
      bprintf b "for (size_t %s = %a; %s<=%a; ++%s) {\n%a\n}"
        counter num min counter num max counter (inst p (k+2)) i

  | Case (e, s) ->
      bprintf b "switch (%a) {\n%a%a}"
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
    indent k (hex_of_bin n) (inst p (k+2)) i indent (k+2)

and affect p k b dst src =
  if src = Unpredictable_exp then string b "unpredictable()"
  else match dst with
    | Reg (Var "d", _) -> bprintf b
        "if (d==PC)\n%aset_pc_raw(proc,%a);\n%aelse\n%aset_reg(proc,d,%a)"
          indent (k+2) (exp p) src indent k indent (k+2) (exp p) src
    | Reg (Num "15", None) -> bprintf b "set_pc_raw(proc,%a)" (exp p) src
    | Reg (e, None) -> bprintf b "set_reg(proc,%a,%a)" (exp p) e (exp p) src
    | Reg (e, Some m) ->
	bprintf b "set_reg_m(proc,%a,%s,%a)" (exp p) e (mode m) (exp p) src
    | CPSR -> (
        match src with
          | SPSR None -> bprintf b "proc->cpsr = *spsr(proc)"
          | SPSR (Some m) -> bprintf b "proc->cpsr = *spsr_m(proc,%s)" (mode m)
          | _ -> bprintf b "set_StatusRegister(&proc->cpsr,%a)" (exp p) src)
    | SPSR None -> (
        match src with
          | CPSR -> bprintf b "*spsr(proc) = proc->cpsr"
          | _ -> bprintf b "set_StatusRegister(spsr(proc),%a)" (exp p) src)
    | SPSR (Some m) -> (
        match src with
          | CPSR -> bprintf b "*spsr_m(proc,%s) = proc->cpsr" (mode m)
          | _ -> bprintf b "set_StatusRegister(spsr_m(proc,%s),%a)" (mode m) (exp p) src)
    | Var v -> bprintf b "%a = %a" (exp p) (Var v) (exp p) src
    | Range (CPSR, Flag (s,_)) ->
        bprintf b "proc->cpsr.%s_flag = %a" s (exp p) src
    | Range (CPSR, Index (Num n)) ->
        bprintf b "proc->cpsr.%s = %a" (cpsr_flag n) (exp p) src
    | Range (CPSR, Bits ("19", "18")) ->
        bprintf b "set_GE_32(&proc->cpsr,%a)" (exp p) src
    | Range (CPSR, Bits ("17", "16")) ->
        bprintf b "set_GE_10(&proc->cpsr,%a)" (exp p) src
    | Range (CPSR, Bits (n1, n2)) ->
        bprintf b "proc->cpsr.%s = %a" (cpsr_field (n1,n2)) (exp p) src
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
      | Inst ->
          bprintf b "%avoid %s(Processor *proc%a)\n{\n%a%a%a\n}\n" comment p
            p.xid
            (list "" prog_arg) p.xgs
            (list "" inreg_load) inregs
            (list "" local_decl) p.xls
            (inst p 2) p.xprog.pinst
      | Mode m ->
          let os = mode_outputs.(m-1)
          and ls' = List.filter (fun (x, _) -> List.mem x optemps) p.xls in
            bprintf b "%avoid %s(Processor *proc%a%a)\n{\n%a%a%a\n}\n" comment p
              p.xid
              (list "" prog_arg) p.xgs
              (list "" prog_out) os
              (list "" inreg_load) inregs
              (list "" local_decl) ls'
              (inst p 2) p.xprog.pinst;;

(* Declaration of the functions. This should be printed in a header file (.h) *)
let decl b p =
  match p.xprog.pkind with
    | Inst  ->
	bprintf b "%aextern void %s(Processor*%a);\nextern bool try_%s(Processor*, uint32_t bincode);\n"
          comment p p.xid
          (list "" prog_arg) p.xgs p.xid
    | Mode m ->
	let os =
          if mode_outputs.(m-1) = [] then (
            let os' = List.filter (fun (x, _) -> not (List.mem x optemps)) p.xls in
              mode_outputs.(m-1) <- os');
          mode_outputs.(m-1)
        in
          bprintf b "%aextern void %s(Processor*%a%a);\n" comment p
            p.xid
            (list "" prog_arg) p.xgs
            (list "" prog_out) os;
          bprintf b "extern bool try_%s(Processor*, uint32_t bincode%a);\n"
            p.xid (list "" prog_out) os;;

(* For some LSM instructions, the operand has side effects that must be executed
 * after the instruction itself *)
let lsm_hack p =
  let rec inst = function
    | Block is -> Block (List.map inst is)
    | If (_, Affect (Reg (Var "n", None), e), None) -> Affect (Var "new_Rn", e)
    | i -> i
  in
  let guard i = (i.iname = "LDM" || i.iname = "STM") && i.ivariant <> Some "2"
  in match p.pkind with
    | Inst when guard p.pident ->
	(* add 'if (W) then Rn = new_Rn' at the end of the main 'if' *)
        let a = If(Var "W",Affect(Reg(Var"n",None),Var"new_Rn"),None) in
        let i = match p.pinst with
          | If (c, Block ids, None) -> If (c, Block (ids @ [a]), None)
          | Block ([x; If (c, Block ids, None)]) ->
	      Block ([x; If (c, Block (ids @ [a]), None)])
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
            | Inst -> is := x::!is);
          aux tl
      | [] -> (!is, ms)
  in aux xs;;

(* get the list of parameters *)
let parameters_of p =
  let rename s =
    if s.[0] = 'R'
    then String.sub s 1 (String.length s -1)
    else match s with
      | "8_bit_immediate" -> "immed_8" (* renamed in preproc_pseudo.sh *)
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
  let _, ps = Array.fold_left aux (0, []) p.xdec in ps;;

(* generate the code extracing the parameters from the instruction code *)
let dec_param p buf (s, a, b) =
  (* exclude "shifter_operand" *)
  if (s, a, b) = ("shifter_operand", 11, 0) then ()
  else
    (* compute the list of used parameters *)
    let gs = p.xgs in
    let gs = match p.xvc with
      | Some e ->
          let vs, _ = V.vars_exp (StrMap.empty, StrMap.empty) e in
            List.merge compare (list_of_map vs) gs
      | None -> gs
    in try
        let t = List.assoc s gs in
          if (s, a, b) = ("cond", 31, 28) then (
            (* special case for cond, because decoding of this field can fail *)
            bprintf buf "  const uint32_t cond_tmp = get_bits(bincode,31,28);\n";
            bprintf buf "  if (cond_tmp>14) return false;\n";
            bprintf buf "  const Condition cond =\n";
            bprintf buf "    ((Condition) cond_tmp);\n"
          ) else if (s, a, b) = ("mode", 4, 0) then (
            (* special case for mode, because decoding of this field can fail *)
            bprintf buf "  const uint32_t mode_tmp = get_bits(bincode,4,0);\n";
            bprintf buf "  Mode mode;\n";
            bprintf buf
              "  if (!decode_mode(&mode,bincode)) return false;\n"
          ) else
            if a = b then
              bprintf buf "  const %s %s = get_bit(bincode,%d);\n" t s a
            else
              bprintf buf "  const %s %s = get_bits(bincode,%d,%d);\n" t s a b
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
      bprintf b "    DEBUG(<<\"decoder choice: %s\\n\");\n" p.xid;
      bprintf b "    assert(!found); found = true;\n  }\n"
  in
    (* Phase B: extract parameters and check validity *)
  let instB b p =
    bprintf b "bool try_%s(Processor *proc, uint32_t bincode) {\n" p.xid;
    (* extract parameters *)
    bprintf b "%a" (list "" (dec_param p)) (parameters_of p);
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
               (list "" local_decl) os m (list "" aux) os
       | None -> ());
    (* execute the instruction *)
    let aux b (s,_) = bprintf b ",%s" s in
    bprintf b "  EXEC(%s(proc%a));\n" p.xid (list "" aux) p.xgs;
    bprintf b "  return true;\n}\n"
  in
  let is' = List.rev is in
    bprintf b "bool decode_and_exec(Processor *proc, uint32_t bincode) {\n";
    bprintf b "  bool found = false;\n";
    bprintf b "%a" (list "" instA) is';
    bprintf b "  return found;\n}\n\n%a"
      (list "\n" instB) is';;

(* declare the try_Mx methods *)
let decl_try b m os =
  bprintf b "\nextern bool try_M%d(Processor*, uint32_t bincode%a);\n"
    (m+1) (list "" prog_out) os;;

(* generate the decoder - modes *)
let dec_modes b ms =
  (* Phase A: check bits fixed by the coding table *)
  let modeA os b p =
    let (mask, value) = mask_value p.xdec in
      bprintf b "  if ((bincode&0x%08lx)==0x%08lx &&\n      try_%s(proc,bincode,%a)) {\n"
        mask value p.xid (list "," print_first) os;
      bprintf b "    assert(!found); found = true;\n  }\n"
  in (* Phase B: extract parameters and check validity *)
  let modeB os b p =
    bprintf b "bool try_%s(Processor *proc, uint32_t bincode%a) {\n"
      p.xid (list "" prog_out) os;
    (* extract parameters *)
    bprintf b "%a" (list "" (dec_param p)) (parameters_of p);
    (* check validity *)
    (match p.xvc with
       | Some e -> bprintf b "  if (!(%a)) return false;\n" (exp p) e
       | None -> ());
    (* execute the mode case *)
    bprintf b "  EXEC(%s(proc,%a,%a));\n" p.xid
      (list "," print_first) p.xgs (list "," print_first) os;
    bprintf b "  return true;\n}\n"
  in (* generate the decoder for mode i *)
  let dec_mode b i ms =
    let ms' = List.rev ms in
    let os = mode_outputs.(i) in
      bprintf b "\nbool try_M%d(Processor *proc, uint32_t bincode%a) {\n"
        (i+1) (list "" prog_out) os;
      bprintf b "  bool found = false;\n%a"
        (list "" (modeA os)) ms';
      bprintf b "  return found;\n}\n\n%a" (list "\n" (modeB os)) ms';
  in Array.iteri (dec_mode b) ms;;

(* main function
 * bn: output file basename, pcs: pseudo-code trees, decs: decoding rules *)
let lib (bn: string) (pcs: prog list) (decs: Codetype.maplist) =
  let pcs' = List.map lsm_hack pcs in (* hack LSM instructions *)
  let decs' = (* remove encodings *)
    let aux x = add_mode (name x) <> DecEncoding in
      List.filter aux decs
  in
  let xs = List.map2 xprog_of pcs' decs' in (* compute extended programs *)
  let is, ms = split xs in (* group by kind *)
    (* create buffers for header file (bh) and source file (bc) *)
  let bh = Buffer.create 10000 and bc = Buffer.create 10000 in
    (* generate the header file *)
    bprintf bh "#ifndef ARM_ISS_H\n#define ARM_ISS_H\n\n";
    bprintf bh "#include \"arm_iss_h_prelude.h\"\n\n";
    bprintf bh "%a" (list "\n" decl) xs;
    Array.iteri (decl_try bh) mode_outputs;
    bprintf bh "\nextern bool decode_and_exec(Processor*, uint32_t bincode);\n";
    bprintf bh "\n#endif // ARM_ISS_H\n";
    (* generate the source file *)
    bprintf bc "#include \"%s.h\"\n#include \"arm_iss_c_prelude.h\"\n\n%a\n%a%a"
      bn (list "\n" prog) xs dec_inst is dec_modes ms;
    (* write buffers to files *)
    let outh = open_out (bn^".h") and outc = open_out (bn^".c") in
      Buffer.output_buffer outh bh; close_out outh;
      Buffer.output_buffer outc bc; close_out outc;;
