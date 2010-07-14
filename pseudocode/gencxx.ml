(**
   SimSoC-Cert, a library on processor architectures for embedded systems.
   See the COPYRIGHTS and LICENSE files.

   Formalization of the ARM architecture version 6 following the:

   ARM Architecture Reference Manual, Issue I, July 2005.

   Page numbers refer to ARMv6.pdf.

   C++ code generator for simulation (see directory ../cxx)
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
  | "0b10111" -> "ARM_Processor::abt"
  | "0b10011" -> "ARM_Processor::svc"
  | _ -> "TODO_hex_of_bin";;

(** C++ types of usual variables *)

let type_of_var = function

  | "S" | "L" | "mmod" | "F" | "I" | "A" | "R" | "x" | "y" | "X" | "U" | "W"
  | "shifter_carry_out" | "opcode25" | "E" -> "bool"

  | "signed_immed_24" | "H" | "shifter_operand" | "alu_out" | "target"
  | "data" | "value" | "diffofproducts" | "address" | "start_address"
  | "physical_address" | "operand" | "opcode" | "byte_mask" | "mask"
  | "sum" | "diff" | "operand1" | "operand2" | "product1" | "product2"
  | "temp" | "diff1" | "diff2" | "diff3" | "diff4" | "invalidhandler"
  | "jpc" | "index" | "end_address" | "new_Rn" -> "uint32_t"

  | "n" | "d" | "m" | "s" | "dHi" | "dLo" | "imod" | "immed_8" | "rotate_imm"
  | "field_mask" | "shift_imm" | "sat_imm" | "rotate" | "cp_num"
  | "immedH" | "immedL" | "offset_8" | "shift" -> "uint8_t"

  | "cond" -> "ARM_Processor::Condition"
  | "mode" -> "ARM_Processor::Mode"
  | "register_list" | "offset_12" -> "uint16_t"
  | "accvalue" | "result" -> "uint64_t"
  | "processor_id" -> "size_t"
  | _ -> "TODO_type_of_var";;

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

let mode_outputs = Array.create 5 [];;

(** Heuristic to chose between signed and unsigned; true means signed *)

let get_signed, set_signed = get_set false;;

(** Add a cast to a signed type *)
let rec to_signed e = match e with
  | Fun ("to_64", [e']) -> Fun ("to_64", [to_signed e'])
  | e' -> Fun ("to_signed", [e']);;

(** Generate the code corresponding to an expression *)

let func = function
  | "CP15_reg1_EEbit" -> "proc.cp15.get_reg1_EEbit"
  | "CP15_reg1_Ubit" -> "proc.cp15.get_reg1_Ubit"
  | "PrivMask" -> "proc.msr_PrivMask"
  | "UserMask" -> "proc.msr_UserMask"
  | "StateMask" -> "proc.msr_StateMask"
  | "UnallocMask" -> "proc.msr_UnallocMask"
  | "GE" -> "proc.cpsr.GE"
  | "v5_and_above" -> "proc.v5_and_above"
  | s -> s;;

let mode m = "ARM_Processor::" ^ Genpc.string_of_mode m;;

let binop = function
  | "and" -> "&&"
  | "or" -> "||"
  | "AND" -> "&"
  | "OR" -> "|"
  | "EOR" -> "^"
  | "NOT" -> "~"
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
  | "15" -> "ARM_Processor::PC"
  | "14" -> "ARM_Processor::LR"
  | "13" -> "ARM_Processor::SP"
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

let rec exp b = function
  | Bin s -> string b (hex_of_bin s)
  | Hex s | Num s -> string b s
  | If_exp (e1, e2, e3) -> bprintf b "(%a? %a: %a)" exp e1 exp e2 exp e3
  | BinOp (e1, ("Rotate_Right"|"Arithmetic_Shift_Right" as op), e2) ->
      exp b (Fun (binop op, [e1; e2]))
  | BinOp (e, "<<", Num "32") ->
      bprintf b "(to_64(%a) << 32)" exp e
  | BinOp (e, ("<"|">=" as op), Num "0") ->
      bprintf b "(%a %s 0)" exp (to_signed e) op
  | BinOp (e1, "*", e2) -> if get_signed ()
    then bprintf b "(to_64(%a) * to_64(%a))" exp (to_signed e1) exp (to_signed e2)
    else bprintf b "(to_64(%a) * to_64(%a))" exp e1 exp e2
  | BinOp (e1, op, e2) -> bprintf b "(%a %s %a)" exp e1 (binop op) exp e2
  | Fun (f, es) -> bprintf b "%s(%a)" (func f) (list ", " exp) es
  | CPSR -> string b "proc.cpsr"
  | SPSR None -> string b "proc.spsr()"
  | SPSR (Some m) -> bprintf b "proc.spsr(%s)" (mode m)
  | Reg (Var s, None) ->
      if List.mem s input_registers
      then bprintf b "old_R%s" s
      else bprintf b "proc.reg(%s)" s
  | Reg (e, None) -> bprintf b "proc.reg(%a)" exp e
  | Reg (e, Some m) -> bprintf b "proc.reg(%a,%s)" exp e (mode m)
  | Var s -> string b s
  | Memory (e, n) -> bprintf b "proc.mmu.read_%s(%a)" (access_type n) exp e
  | Range (CPSR, Flag (s,_)) -> bprintf b "proc.cpsr.%s_flag" s
  | Range (CPSR, Index (Num s)) -> bprintf b "proc.cpsr.%s" (cpsr_flag s)
  | Range (e1, Index e2) -> bprintf b "((%a>>%a)&1)" exp e1 exp e2
  | Range (e, Bits (n1, n2)) ->
      begin match n1, n2 with
        | "15", "0" -> bprintf b "get_half_0(%a)" exp e
        | "31", "16" -> bprintf b "get_half_1(%a)" exp e
        | "7", "0" -> bprintf b "get_byte_0(%a)" exp e
        | "15", "8" -> bprintf b "get_byte_1(%a)" exp e
        | "23", "16" -> bprintf b "get_byte_2(%a)" exp e
        | "31", "24" -> bprintf b "get_byte_3(%a)" exp e
        | ("63"|"47"), _ -> bprintf b "get_bits64(%a,%s,%s)" exp e n1 n2
        | _ -> bprintf b "get_bits(%a,%s,%s)" exp e n1 n2
      end
  | Coproc_exp (e, f, es) ->
      bprintf b "proc.coproc(%a)->%s(%a)" exp e (func f) (list ", " exp) es
  | _ -> string b "TODO(\"exp\")";;

(** Generate the body of an instruction function *)

let rec inst k b = function
  | Block _ | For _ | While _ | If _ | Case _ as i ->
      bprintf b "%a%a" indent k (inst_aux k) i
  | i -> bprintf b "%a%a;" indent k (inst_aux k) i

and inst_aux k b = function
  | Unpredictable -> string b "unpredictable()"
  | Affect (dst, src) -> affect k b dst src
  | Proc (f, es) -> bprintf b "%s(%a)" f (list ", " exp) es
  | Assert e -> bprintf b "assert(%a)" exp e
  | Coproc (e, f, es) ->
      bprintf b "proc.coproc(%a)->%s(%a)" exp e (func f) (list ", " exp) es

  | Block [] -> ()
  | Block (Block _ | For _ | While _ | If _ | Case _ as i :: is) ->
      bprintf b "%a\n%a" (inst_aux k) i (list "\n" (inst k)) is
  | Block (i :: is) ->
      bprintf b "%a;\n%a" (inst_aux k) i (list "\n" (inst k)) is

  | While (e, i) -> bprintf b "while (%a)\n%a" exp e (inst (k+2)) i

  | For (counter, min, max, i) ->
      bprintf b "for (size_t %s = %a; %s<=%a; ++%s) {\n%a\n}"
        counter num min counter num max counter (inst (k+2)) i

  | Case (e, s) ->
      bprintf b "switch (%a) {\n%a%a}"
        exp e (list "" (case_aux k)) s indent k

  | If (e, (Block _|If _ as i), None) ->
      bprintf b "if (%a) {\n%a\n%a}" exp e (inst (k+2)) i indent k
  | If (e, i, None) -> bprintf b "if (%a)\n%a" exp e (inst (k+2)) i

  | If (e, (Block _|If _ as i1), Some (Block _|If _ as i2)) ->
      bprintf b "if (%a) {\n%a\n%a} else {\n%a\n%a}"
	exp e (inst (k+2)) i1 indent k (inst (k+2)) i2 indent k
  | If (e, (Block _|If _ as i1), Some i2) ->
      bprintf b "if (%a) {\n%a\n%a} else\n%a"
	exp e (inst (k+2)) i1 indent k (inst (k+2)) i2
  | If (e, i1, Some (Block _|If _ as i2)) ->
      bprintf b "if (%a)\n%a\n%aelse {\n%a\n%a}"
	exp e (inst (k+2)) i1 indent k (inst (k+2)) i2 indent k
  | If (e, i1, Some i2) ->
      bprintf b "if (%a)\n%a\n%aelse\n%a"
	exp e (inst (k+2)) i1 indent k (inst (k+2)) i2

and case_aux k b (n, i) =
  bprintf b "%acase %s:\n%a\n%abreak;\n"
    indent k (hex_of_bin n) (inst (k+2)) i indent (k+2)

and affect k b dst src =
  if src = Unpredictable_exp then string b "unpredictable()"
  else match dst with
    | Reg (Var "d", _) -> bprintf b
        "if (d==ARM_Processor::PC)\n%aproc.set_pc_raw(%a);\n%aelse\n%aproc.reg(d) = %a"
          indent (k+2) exp src indent k indent (k+2) exp src
    | Reg (Num "15", None) -> bprintf b "proc.set_pc_raw(%a)" exp src
    | Reg (e, None) -> bprintf b "proc.reg(%a) = %a" exp e exp src
    | Reg (e, Some m) ->
	bprintf b "proc.reg(%a,%s) = %a" exp e (mode m) exp src
    | CPSR -> bprintf b "proc.cpsr = %a" exp src
    | SPSR _ as e -> bprintf b "%a = %a" exp e exp src
    | Var v -> bprintf b "%a = %a" exp (Var v) exp src
    | Range (CPSR, Flag (s,_)) ->
        bprintf b "proc.cpsr.%s_flag = %a" s exp src
    | Range (CPSR, Index (Num n)) ->
        bprintf b "proc.cpsr.%s = %a" (cpsr_flag n) exp src
    | Range (CPSR, Bits ("19", "18")) ->
        bprintf b "proc.cpsr.set_GE_32(%a)" exp src
    | Range (CPSR, Bits ("17", "16")) ->
        bprintf b "proc.cpsr.set_GE_10(%a)" exp src
    | Range (CPSR, Bits (n1, n2)) ->
        bprintf b "proc.cpsr.%s = %a" (cpsr_field (n1,n2)) exp src
    | Range (e1, Bits (n1, n2)) ->
        inst_aux k b (Proc ("set_field", [e1; Num n1; Num n2; src]))
    | Memory (addr, n) ->
        inst_aux k b (Proc ("proc.mmu.write_" ^ access_type n, [addr; src]))
    | Range (e, Index n) -> inst_aux k b (Proc ("set_bit", [e; n; src]))
    | _ -> string b "TODO(\"affect\")";;

(** Generate a function modeling an instruction of the processor *)

let prog_var b s = bprintf b "<%s>" s;;

let prog_arg b (v,t) = bprintf b "const %s %s" t v;;

let prog_out b (v,t) = bprintf b "%s &%s" t v;;

let local_decl b (v,t) = bprintf b "  %s %s;\n" t v;;

let inreg_load b s =
  bprintf b "  const uint32_t old_R%s = proc.reg(%s);\n" s s;;

let comment b p = bprintf b "// %a\n" Genpc.name p.xprog;;

let arg_sep l l' = match l, l' with _::_, _::_ -> ",\n    " | _ -> "";;

let print_first b (s, _) = string b s;;

(* Defintion of the functions. This should be printed in a source file (.cpp) *)
let prog b p =
  let ss = List.fold_left (fun l (s, _) -> s::l) [] p.xgs in
  let inregs = List.filter (fun x -> List.mem x input_registers) ss in
    match p.xprog.pkind with
      | Inst ->
          set_signed (p.xid.[0] = 'S');
          bprintf b "%avoid ARM_ISS::%s(%a)\n{\n%a%a%a\n}\n" comment p
            p.xid
            (list ",\n    " prog_arg) p.xgs
            (list "" inreg_load) inregs
            (list "" local_decl) p.xls
            (inst 2) p.xprog.pinst
      | Mode m ->
          let os = mode_outputs.(m-1)
          and ls' = List.filter (fun (x, _) -> List.mem x optemps) p.xls in
            bprintf b "%avoid ARM_ISS::%s(%a%s%a)\n{\n%a%a%a\n}\n" comment p
              p.xid
              (list ",\n    " prog_arg) p.xgs
              (arg_sep p.xgs os)
              (list ",\n    " prog_out) os
              (list "" inreg_load) inregs
              (list "" local_decl) ls'
              (inst 2) p.xprog.pinst;;

(* Declaration of the functions. This should be printed in a header file (.hpp) *)
let decl b p =
  match p.xprog.pkind with
    | Inst  ->
	bprintf b "  %a  void %s(%a);\n  bool try_%s(uint32_t bincode);\n"
          comment p p.xid
          (list ",\n    " prog_arg) p.xgs p.xid
    | Mode m ->
	let os =
          if mode_outputs.(m-1) = [] then (
            let os' = List.filter (fun (x, _) -> not (List.mem x optemps)) p.xls in
              mode_outputs.(m-1) <- os');
          mode_outputs.(m-1)
        in
          bprintf b "  %a  void %s(%a%s%a);\n" comment p
            p.xid
            (list ",\n    " prog_arg) p.xgs
            (arg_sep p.xgs os)
            (list ",\n    " prog_out) os;
          bprintf b "  bool try_%s(uint32_t bincode,\n    %a);\n"
            p.xid (list ",\n    " prog_out) os;;

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
            bprintf buf "  const ARM_Processor::Condition cond =\n";
            bprintf buf "    static_cast<ARM_Processor::Condition>(cond_tmp);\n"
          ) else if (s, a, b) = ("mode", 4, 0) then (
            (* special case for mode, because decoding of this field can fail *)
            bprintf buf "  const uint32_t mode_tmp = get_bits(bincode,4,0);\n";
            bprintf buf "  ARM_Processor::Mode mode;\n";
            bprintf buf
              "  if (!ARM_Processor::decode_mode(bincode,mode)) return false;\n"
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
      bprintf b "  if ((bincode&0x%08lx)==0x%08lx && try_%s(bincode)) {\n"
        mask value p.xid;
      bprintf b "    DEBUG(<<\"decoder choice: %s\\n\");\n" p.xid;
      bprintf b "    assert(!found); found = true;\n  }\n"
  in
    (* Phase B: extract parameters and check validity *)
  let instB b p =
    bprintf b "bool ARM_ISS::try_%s(uint32_t bincode) {\n" p.xid;
    (* extract parameters *)
    bprintf b "%a" (list "" (dec_param p)) (parameters_of p);
    (* check validity *)
    (match p.xvc with
       | Some e -> bprintf b "  if (!(%a)) return false;\n" exp e
       | None -> ());
    (* decode the mode *)
    (match p.xmode with
       | Some m ->
           let os = mode_outputs.(m-1) in
             bprintf b "%a  if (!try_M%d(bincode,%a)) return false;\n"
               (list "" local_decl) os m (list "," print_first) os
       | None -> ());
    (* execute the instruction *)
    bprintf b "  EXEC(%s(%a));\n" p.xid (list "," print_first) p.xgs;
    bprintf b "  return true;\n}\n"
  in
  let is' = List.rev is in
    bprintf b "bool ARM_ISS::decode_and_exec(uint32_t bincode) {\n";
    bprintf b "  bool found = false;\n";
    bprintf b "%a" (list "" instA) is';
    bprintf b "  return found;\n}\n\n%a"
      (list "\n" instB) is';;

(* declare the try_Mx methods *)
let decl_try b m os =
  let sep = ",\n              " in
    bprintf b "\n  bool try_M%d(uint32_t bincode%s%a);\n"
      (m+1) sep (list sep prog_out) os;;

(* generate the decoder - modes *)
let dec_modes b ms =
  (* Phase A: check bits fixed by the coding table *)
  let modeA os b p =
    let (mask, value) = mask_value p.xdec in
      bprintf b "  if ((bincode&0x%08lx)==0x%08lx &&\n      try_%s(bincode,%a)) {\n"
        mask value p.xid (list "," print_first) os;
      bprintf b "    assert(!found); found = true;\n  }\n"
  in (* Phase B: extract parameters and check validity *)
  let modeB os b p =
    bprintf b "bool ARM_ISS::try_%s(uint32_t bincode,\n    %a) {\n"
      p.xid (list ",\n    " prog_out) os;
    (* extract parameters *)
    bprintf b "%a" (list "" (dec_param p)) (parameters_of p);
    (* check validity *)
    (match p.xvc with
       | Some e -> bprintf b "  if (!(%a)) return false;\n" exp e
       | None -> ());
    (* execute the mode case *)
    bprintf b "  EXEC(%s(%a,%a));\n" p.xid
      (list "," print_first) p.xgs (list "," print_first) os;
    bprintf b "  return true;\n}\n"
  in (* generate the decoder for mode i *)
  let sep = ",\n                     " in
  let dec_mode b i ms =
    let ms' = List.rev ms in
    let os = mode_outputs.(i) in
      bprintf b "\nbool ARM_ISS::try_M%d(uint32_t bincode%s%a) {\n"
        (i+1) sep (list sep prog_out) os;
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
    bprintf bh "#include \"arm_iss_base.hpp\"\n\n";
    bprintf bh "struct ARM_ISS: ARM_ISS_Base {\n\n%a" (list "\n" decl) xs;
    Array.iteri (decl_try bh) mode_outputs;
    bprintf bh "\n  bool decode_and_exec(uint32_t bincode);\n};\n";
    (* generate the source file *)
    bprintf bc "#include \"%s.hpp\"\n#include \"common.hpp\"\n\n%a\n%a%a"
      bn (list "\n" prog) xs dec_inst is dec_modes ms;
    (* write buffers to files *)
    let outh = open_out (bn^".hpp") and outc = open_out (bn^".cpp") in
      Buffer.output_buffer outh bh; close_out outh;
      Buffer.output_buffer outc bc; close_out outc;;

(* REMOVE:
 * alternative main function used to compute some statistics *)
(* let xlib bn pcs decs = *)
(*   let b = Buffer.create 10000 in *)
(*   let (is, es, ms) = dec_split decs in *)
(*     bprintf b "%d instructions, %d encoding" (List.length is) (List.length es); *)
(*     Array.iteri (fun i l -> bprintf b ", %d mode %d" (List.length l) (i+1)) ms; *)
(*     bprintf b "\n%d decoding rules\n%d instructions or addressing modes\n" *)
(*       (List.length decs) (List.length pcs); *)
(*     let stats = Array.create 32 0 in *)
(*     let poscontent (_, pcs) = *)
(*       let bit i pc = match pc with *)
(*         | Codetype.Shouldbe _ -> stats.(i) <- stats.(i) + 1 *)
(*         | _ -> () *)
(*       in Array.iteri bit pcs *)
(*     in *)
(*       List.iter poscontent is; *)
(*       Array.iteri (fun i n -> bprintf b "bit %d is a \"Souldbe\" %d times.\n" i n) stats; *)
(*       let out = open_out (bn^".txt") in *)
(*         Buffer.output_buffer out b; close_out out;; *)
