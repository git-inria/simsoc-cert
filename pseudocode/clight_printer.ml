(**
SimSoC-Cert, a library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Generate the ISS in Clight.
*)

open Ast;;
open Ast_clight;;
open Printf;;
open Util;;
open Flatten;;

let type_of_var = function

  | "S" | "L" | "mmod" | "F" | "I" | "A" | "R" | "x" | "y" | "X" | "U" | "W"
  | "shifter_carry_out" | "E" -> "unsigned char"
      
  | "n" | "d" | "m" | "s" | "dHi" | "dLo" | "imod" | "immed_8" | "rotate_imm"
  | "field_mask" | "shift_imm" | "sat_imm" | "rotate" | "cp_num"
  | "immedH" | "immedL" | "offset_8" | "shift" 
  | "opcode_1" | "opcode_2" | "CRn" | "CRm" -> "unsigned char"

  | "cond" -> "int"
  | "old_mode" | "mode" -> "int"
  | "accvalue" | "result" | "value" -> "unsigned long"
  | _ -> "unsigned int";;

let type_of_signedness = function
  | Unsigned -> "unsigned"
  | Signed -> "signed";;


module G = struct

  type typ = string;;

  let global_type = type_of_var;;

  let type_of_size = function
    | Byte -> "char"
    | Half -> "half"
    | Word -> "int";;

  let local_type s _ = type_of_var s

  let rec explicit_annot_type ty _ = match (typ_trans ty) with
    | Int (sg, sz) -> (type_of_signedness sg)^" "^(type_of_size sz)
    | Float sz -> if sz = F32 then "float" else "double"
    | Void -> "void"
    | _ -> "not support"
  
  let case_type = "int";;

end;;

module V = Ast.Make(G);;

let prog_trans p = 
  let gs, ls = V.vars p.pinst and id = Flatten.str_ident p in
  {cl_pref = p.pref; 
   cl_pkind = p.pkind;
   cl_pid = id;
   cl_pident = p.pident; 
   cl_pidents = p.pidents;
   cl_params = gs;
   cl_vars = ls;
   cl_tmpvars = [];
   cl_pfuncs = stm_trans (p.pinst)};;

let func = function
  | "not" -> "!"
  | "NOT" -> "~"
  | "GE" -> "get_GE"
  | "TLB" -> "slv6_TLB"
  | s -> s;;

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
  | _ -> "TODO_binop";;

let reg_id = function
  | "15" -> "PC"
  | "14" -> "LR"
  | "13" -> "SP"
  | n -> n;;

let implicit_arg = function
  | "ConditionPassed" -> "&(*proc).cpsr, "
  | "write_word" | "write_half" | "write_byte" -> "(*proc).cpsr, "
  | "CP15_reg1_EEbit" | "CP15_reg1_Ubit" | "CP15_reg1_Vbit" -> "&(*proc).cp15"
  | "set_bit" | "set_field" -> "addr_of_"
  | "InAPrivilegedMode" | "CurrentModeHasSPSR" | "address_of_next_instruction"
  | "address_of_current_instruction" | "high_vectors_configured" -> "proc"
  | "set_reg_m" -> "proc, "
  | _ -> "";;

let rec types _s b = function
  | Int (sg, sz) -> bprintf b "%s %s" (type_of_signedness sg) (G.type_of_size sz)
  | Float sz -> string b (if sz = F32 then "float" else "double")
  | Void -> string b "void"
  | Pointer t -> bprintf b "%a *" (types _s) t
  | Function t -> bprintf b "%a" (types _s) t
  | Struct (id, flds) -> bprintf b "struct %s {\n%a}" id (fields _s) flds
  | Union (id, flds) -> bprintf b "union %s {\n%a}" id (fields _s) flds
  | Comp_pointer id -> bprintf b "*%s" id
  | Other -> string b "not support"

and fields _s b = function
  | Fnil -> string b ""
  | Fcons (id, t, fld) -> bprintf b "%a %s;\n%a" (types _s) t id (fields _s) fld
;;

let rec print_exp _s b = function
  | Eid id -> string b id
  | Eint i -> string b i
  | Efloat f -> string b f
  | Eunop (op, e) -> bprintf b "%s %a" op (print_exp _s) e
  | Ebinop (e1, op, e2) -> bprintf b "(%a %s %a)" 
      (print_exp _s) e1 (binop op) (print_exp _s) e2
  | Epointderef e -> bprintf b "(*%a)" (print_exp _s) e
  | Efieldacc (e, id) -> bprintf b "%a.%s" (print_exp _s) e id
  | Eaddrof e -> bprintf b "&%a" (print_exp _s) e
  | Etypecast (t, e) -> bprintf b "(%a)%a"
      (types "") t (print_exp _s) e
  | Econd (e1, e2, e3) -> bprintf b "(%a) ? %a : %a" 
      (print_exp _s) e1 (print_exp _s) e2 (print_exp _s) e3
  | Efun (e, elst) -> 
      begin match e with
        | Eid str -> bprintf b "%s(%s%a)" str (implicit_arg str)
            (list ", " (print_exp _s)) elst
        | _ -> string b "TODOefun"
      end
  | ETODO -> string b "TODOprint_exp" 
;;

let rec print_statement lst b = function
  | Sskip -> string b ""
  | Svardel (t, e) -> bprintf b "%a %a;\n" 
      (types "") t (print_exp' lst) e
  (*| Sassign (Efun (Eid "reg", [Eid str; e1]), e2) ->
      begin match str with
        | "d" -> 
            bprintf b "set_reg_or_pc(%s, %a, %a);\n" 
              str (print_exp' lst) e1 
              (print_exp' lst) e2
        | _ -> 
            bprintf b "set_reg(%s, %a, %a);\n" 
              str (print_exp' lst) e1 
              (print_exp' lst) e2
      end*)
  | Sassign (e1, e2) -> bprintf b "%a = %a;\n" 
      (print_exp' lst) e1 (print_exp' lst) e2
  | Sfuncall (Some id, e, lstexp) ->
      bprintf b "%s= %a (%a);\n" 
        id (print_exp' lst) e (list "" (print_exp' lst)) lstexp
  | Sfuncall (None, e, lstexp) -> bprintf b "%a (%a);\n" 
      (print_exp' lst) e (list " " (print_exp' lst)) lstexp
  | Ssequence (stm1, stm2) -> begin match stm2 with
      | Sskip -> bprintf b "%a" (print_statement lst) stm1
      | _ -> bprintf b "%a%a" (print_statement lst) stm1
          (print_statement lst) stm2
    end
  | Sifthenelse (e, stm1, stm2) -> 
      begin match stm2 with
        | Sskip -> bprintf b "if (%a){\n%a}\n" 
            (print_exp' lst) e (print_statement lst) stm1
        | stm2 -> bprintf b "if (%a){\n%a}\nelse{\n%a}\n"
            (print_exp' lst) e (print_statement lst) stm1 
              (print_statement lst) stm2
      end
  | Sswitch (e, lb) -> bprintf b "switch (%a) {\n %a}\n" 
      (print_exp' lst) e (print_lable lst) lb
  | Swhile (e, stm) -> bprintf b "while (%a) {\n%a}\n" 
      (print_exp' lst) e (print_statement lst) stm
  | Sfor (stm1, e, stm2, stm) -> bprintf b "for (%a, %a, %a) {\n%a}\n"
      (print_statement lst) stm1 (print_exp' lst) e 
        (print_statement lst) stm2
        (print_statement lst) stm
  | Sincrease e -> bprintf b "%a++;\n" (print_exp' lst) e
  | Sreturn (Some e) -> bprintf b "return %a;\n" (print_exp' lst) e
  | Sreturn None -> string b "return;\n"
  | STODO -> string b "TODOprintstm\n"

and print_lable _s b = function
  | SDefault stm -> bprintf b "default:\n%a\n" (print_statement _s) stm
  | SCase (i, stm, lb) -> bprintf b "case %d:\n%a\nbreak;\n%a\n" i (print_statement _s) stm
      (print_lable _s) lb

and print_exp' lst b e = 
  try bprintf b "t__%d" (List.assoc e lst) with Not_found -> print_exp lst b e
;;

let cl_params _s b (p, t) =
  bprintf b "%s %s" t p;;

let inreg_del b s =
  bprintf b "unsigned int old_R%s = reg(proc,%s);\n" s s;;

let inreg_load b n s =
  bprintf b "%s = reg(proc,%s);\n" n s;;


let rec build_tbl lst s =
    match s with
      | Svardel (_, e) -> tmpvar lst e
      | Sassign (e1, e2) -> tmpvar (tmpvar lst e1) e2
      | Sfuncall (_ , e, lstexp) ->
          tmpvar (List.fold_left tmpvar lst lstexp) e
      | Ssequence (stm1, stm2) -> (build_tbl lst stm1) @ (build_tbl lst stm2)
      | Sifthenelse (e, stm1, stm2) -> 
          tmpvar (build_tbl lst stm1 @ (build_tbl lst stm2)) e
      | Sswitch (e, _) -> tmpvar lst e
      | Swhile (e, stm) -> tmpvar (build_tbl lst stm) e
      | Sfor (stm1, e, stm2, stm) -> 
          tmpvar ((build_tbl lst stm1) @ (build_tbl lst stm2) @ (build_tbl lst stm)) e
      | Sincrease e -> tmpvar lst e
      | Sreturn (Some e) -> tmpvar lst e
      | _ -> lst

and tmpvar lst = function
  | Eunop (_, e) -> tmpvar' lst e
  | Ebinop (e1, _, e2) -> tmpvar' (tmpvar' lst e1) e2
  | Epointderef e -> tmpvar' lst e
  | Efieldacc (e, _) -> tmpvar' lst e
  | Econd (e1, e2, e3) -> tmpvar' (tmpvar' (tmpvar' lst e1) e2) e3
  | Efun (e, _) -> tmpvar' lst e
  | _ -> lst

and tmpvar' lst = function
  | Efun _ as e -> lst @ [e, List.length lst + 1]
  | _ -> lst
;;

let typ_of_fun = function
  | Efun (Eid "set_reg", _) -> "unsigned int"
  | _ -> "unsigned char"
;;

let decl_tmpvars b (e, n) =
  bprintf b "%s t__%d;" (typ_of_fun e) n;;

let load_tmpvars _s b (e, n) =
  bprintf b "t__%d = %a;" n (print_exp _s) e;;

let print_clprog _s b p =
  let gs, ls = V.vars p.pinst and id = Flatten.str_ident p in
  let ss = List.fold_left (fun l (s, _) -> s::l) [] gs in
  let inregs = List.filter (fun x -> List.mem x input_registers) ss in
  (*let tbl = build_tbl [] (stm_trans p.pinst) in*)
  bprintf b
    "void slv6_%s(struct SLv6_Processor *proc, %a)\n{\n%a%a\n%a}\n\n" id
    (list ",\n  " (cl_params _s)) gs
    (list ";\n" (cl_params _s)) ls
    (*(list "\n" decl_tmpvars) tbl*)
    (*(list "\n" (load_tmpvars _s)) tbl*) 
    (list "\n" inreg_del) inregs
    (print_statement []) (spcfun_trans (stm_trans p.pinst))
;;


let print_prog ({ body = pcs ; header = _ } : program) _ss _decs =
  let b = Buffer.create 10000 in
  (*let fs: fprog list = List.rev (flatten pcs ss decs) in*)
  match pcs with
    | [] -> string b "nil"
    | _ -> List.iter (print_clprog [] b) pcs;
        Buffer.output_buffer stdout b;;
