(**
SimSoC-Cert, a library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Pseudocode abstract syntax tree for clight.
*)

open Util;;
open Ast;;
open Clight;;
open Csyntax;;
open Datatypes;;


let input_registers = ["n"; "m"; "s"; "dLo"];;

let mode m = Genpc.string_of_mode m;;

(* Transformation form Pseudocode type_param to Csyntax typ*)
let rec typ_trans (t: Ast.type_param) =
  match t with
    | Ast.Tint -> Tint (I32, Signed)
    | Tlong -> Tint (I32, Signed)
    | Ast.Tfloat -> Tfloat F32
    | Tdouble -> Tfloat F64
    | Ast.Tvoid -> Tvoid
    | Tchar -> Tint (I8, Signed)
    | Tbool -> Tint (I8, Signed)
    | Tunsigned -> Tint (I32, Unsigned)
    | Tunsigned_long -> Tint (I32, Unsigned)
    | Tunsigned_char -> Tint (I8, Unsigned)
    | Tunsigned_short -> Tint (I16, Unsigned)
    | Tunsigned_int -> Tint (I32, Unsigned)
;;

(* Operations transformation, from string to Csyntax type*)
let unop_trans = function
  | "not" -> Onotbool
  | "NOT" -> Onotint
  | "-" -> Oneg
  | _ -> Oneg;;

let binop_trans = function
  | "and" -> Oand
  | "or" -> Oor
  | "AND" -> Oand
  | "OR" | "|" -> Oor
  | "EOR" -> Oxor
  | "Logical_Shift_Left" -> Oshl
  | "Logical_Shift_Right" -> Oshr
  | "==" -> Oeq
  | "!=" -> One
  | ">=" -> Oge
  | "<" -> Olt
  | "+" -> Oadd
  | "-" -> Osub
  | "<<" -> Oshl
  | "*" -> Omul
  | _ -> Oand;;

(* Number expressions, from string to Z*)
let num str = Camlcoq.z_of_camlint (Int32.of_int (int_of_string str));;
let bin str = Camlcoq.z_of_camlint (Int32.of_int (int_of_string ("0b"^str)));;
let hex str = Camlcoq.z_of_camlint (Int32.of_int (int_of_string ("0x"^str)));;

(* From ident name to ident number*)
let pos_of_Z (z: BinInt.coq_Z) = match z with
  | BinInt.Z0 -> BinPos.Coq_xH
  | BinInt.Zpos p -> p
  | BinInt.Zneg n -> n

let rec idn lst str =
  match lst with
    | [] -> pos_of_Z (Camlcoq.z_of_camlint (Int32.of_int (List.length lst)))
    | (h,_) :: t ->  if h = str then 
        pos_of_Z (Camlcoq.z_of_camlint (Int32.of_int (List.length lst - List.length t)))
      else idn t str;;

(* Transformation form Pseudocode expr to Clight expr*)
let rec exp_trans' lst = function
  | Num str -> Econst_int (num str, Tint (I32, Signed))
  | Hex str -> Econst_int (hex str, Tint (I32, Signed))
  | Bin str -> Econst_int (bin str, Tint (I32, Signed))
  | Float_zero -> Econst_float (0.0, Tfloat F32)
  | Var str -> Clight.Evar (idn lst str, Tint (I8, Unsigned))
  | If_exp (e1, e2, e3) -> 
(*Econdition of expr * expr * expr * coq_type*)
      Clight.Econdition 
        (exp_trans' lst e1,exp_trans' lst e2,exp_trans' lst e3, Tint (I8, Unsigned))
  | BinOp (e1, str, e2) -> 
      Clight.Ebinop 
        (binop_trans str, exp_trans' lst e1, exp_trans' lst e2, Tint (I32, Unsigned))
  | Fun _|CPSR|SPSR _|Range _|Unaffected|Unpredictable_exp|Memory _|Coproc_exp _|Reg _
      -> Clight.Evar (idn lst "Etodo", Tvoid)
;;


let rec stm_trans' lst = function
  | Block insts -> begin match insts with
      | [] -> Clight.Sskip
      | i :: is -> Clight.Ssequence (stm_trans' lst i, stm_trans' lst (Block is))
    end
  | Let (_, _, insts, _) -> stm_trans' lst (Block insts)
  | Unpredictable -> Clight.Scall (None, Clight.Evar (idn lst "unpredictable", Tvoid), [])
  | Affect (Reg (Var s, None), e') ->
      begin match s with
        | "d" -> Clight.Scall (None, 
                               Clight.Evar (idn lst "set_reg_or_pc", Tvoid),
                               [Clight.Evar (idn lst "proc", Tint (I32, Unsigned));
                                Clight.Evar (idn lst "d", Tint (I32, Unsigned)); 
                                exp_trans' lst e'])
        | "15" -> Clight.Scall (None, 
                                Clight.Evar (idn lst "set_pc_raw", Tvoid), 
                                [Clight.Evar (idn lst"proc", Tint (I32, Unsigned)); 
                                 exp_trans' lst e'])
        | _ -> Clight.Scall (None, 
                        Clight.Evar (idn lst "set_reg", Tvoid), 
                        [Clight.Evar (idn lst "proc", Tint (I32, Unsigned));
                         Clight.Evar (idn lst "d", Tint (I32, Unsigned)); exp_trans' lst e'])
      end
  | Affect (Reg (Var s, Some m), e') ->
      Clight.Scall (None, Clight.Evar (idn lst "set_reg_m",Tvoid),  
                        [Clight.Evar (idn lst "proc", Tint (I32, Unsigned));
                         Clight.Evar (idn lst s, Tint (I32, Unsigned)); 
                         Clight.Evar (idn lst (mode m), Tint (I32, Unsigned)); 
                         exp_trans' lst e'])
  | Affect (Range (e1, Index e2), e') -> 
      Clight.Scall (None, Clight.Evar (idn lst "set_bit", Tint (I32, Unsigned)), 
             [exp_trans' lst e1; exp_trans' lst e2; exp_trans' lst e'])
  | Affect (Range (e, Bits (n1, n2)), e') ->
      Clight.Scall (None, Clight.Evar (idn lst "set_bits", Tint (I32, Unsigned)), 
             [exp_trans' lst e; Econst_int (num n1, Tint (I32, Unsigned));
              Econst_int (num n2, Tint (I32, Unsigned)); exp_trans' lst e'])
  | Affect (CPSR, e') -> 
      begin match e' with
        | SPSR None -> 
            Clight.Scall (None, Clight.Evar (idn lst "copy_StatusRegister", Tvoid),
                   [Clight.Efield 
                      (Clight.Eaddrof (Clight.Evar (idn lst "proc", 
                                                    Tstruct (idn lst "SLv6_Processor", Fnil)), 
                                       Tint (I32, Unsigned)), 
                       idn lst "cpsr", Tint (I32, Unsigned));
                   Clight.Evar (idn lst "spsr", 
                                Tstruct (idn lst "SLv6_StatusRegister", 
                                         Fcons (idn lst "proc",
                                                Tstruct (idn lst "SLv6_Processor", Fnil), Fnil)))])
        | SPSR (Some m) -> 
            Clight.Scall (None, Clight.Evar (idn lst "copy_StatusRegister", Tvoid),
                   [Clight.Efield 
                      (Clight.Eaddrof 
                         (Clight.Evar (idn lst "proc", Tstruct (idn lst "SLv6_Processor", Fnil)), 
                          Tint (I32, Unsigned)), idn lst "cpsr", 
                       Tint (I32, Unsigned));
                   Clight.Evar (idn lst "spsr_m", 
                                Tstruct (idn lst "SLv6_StatusRegister", 
                                         Fcons (idn lst "proc", 
                                                Tstruct (idn lst "SLv6_Processor", 
                                                         Fcons (idn lst (mode m), 
                                                                Tint (I32, Unsigned), 
                                                                Fnil)), Fnil)))])
        | e' -> Clight.Scall (None, Clight.Evar (idn lst "set_StatusRegister",Tvoid), 
                              [exp_trans' lst e'])
      end
  | Affect (SPSR None, e') ->
      begin match e' with
        | CPSR -> 
            Clight.Scall (None, Clight.Evar (idn lst "copy_StatusRegister",Tvoid),
                   [Clight.Evar (idn lst "spsr", Tstruct (idn lst "SLv6_StatusRegister", 
                                           Fcons (idn lst "proc", 
                                                  Tstruct (idn lst "SLv6_Processor", Fnil), 
                                                  Fnil)));
                    Clight.Efield 
                      (Clight.Eaddrof (Clight.Evar (idn lst "proc", 
                                                    Tstruct (idn lst "SLv6_Processor", Fnil)), 
                                       Tint (I32, Unsigned)), 
                                   idn lst "cpsr", Tint (I32, Unsigned))])
        | e' -> Clight.Scall (None, Clight.Evar (idn lst "set_StatusRegister", Tvoid), 
                              [exp_trans' lst e'])
      end
  | Affect (SPSR (Some m), e') ->
      begin match e' with
        | CPSR -> 
            Clight.Scall (None, Clight.Evar (idn lst "copy_StatusRegister", Tvoid),
                   [Clight.Evar (idn lst "spsr_m", Tstruct (idn lst "SLv6_StatusRegister", 
                                           Fcons (idn lst "proc", 
                                                  Tstruct (idn lst "SLv6_Processor", 
                                                           Fcons (idn lst (mode m), 
                                                                  Tint (I32, Unsigned), 
                                                                  Fnil)), 
                                                  Fnil)));
                    Clight.Efield (Clight.Eaddrof 
                                     (Clight.Evar (idn lst "proc", 
                                                   Tstruct (idn lst "SLv6_Processor", Fnil)), 
                                      Tint (I32, Unsigned)), idn lst "cpsr", 
                                   Tint (I32, Unsigned))])
        | e' -> Clight.Scall (None, Clight.Evar (idn lst "set_StatusRegister", Tvoid), 
                              [exp_trans' lst e'])
      end
  | Affect (e1, e2) -> Sassign (exp_trans' lst e1, exp_trans' lst e2)
  | Return e -> Clight.Sreturn (Some (exp_trans' lst e))
  | Case (e, s, o) ->
      Clight.Sswitch (exp_trans' lst e, switch_aux lst s o)
  | Coproc (e, f, es) -> 
      Clight.Scall (None, Clight.Evar (idn lst f, Tvoid),
                    List.map (exp_trans' lst) ([e]@es))
  | For (counter, min, max, i) ->
      Clight.Ssequence 
        (stm_trans' lst i,
         Clight.Sfor' 
           (Clight.Ebinop (Olt, Clight.Evar (idn lst counter, Tint (I32, Unsigned)),
                           Econst_int (num max, Tint (I32, Unsigned)), Tint (I32, Unsigned)),
            Clight.Sassign (Clight.Evar (idn lst counter, Tint (I32, Unsigned)),
                            Econst_int (num min, Tint (I32, Unsigned))),
            Clight.Sassign (Clight.Evar (idn lst counter, Tint (I32, Unsigned)),
                            Clight.Ebinop (Oadd, Clight.Evar (idn lst counter, 
                                                              Tint (I32, Unsigned)),
                                           Econst_int (num "1", Tint (I8, Unsigned)),
                                           Tint (I32, Unsigned)))))
  | Assert e -> Clight.Scall (None, Clight.Evar (idn lst "_assert_fail", Tvoid), 
                              [exp_trans' lst e])
  | While (e, i) -> Clight.Sdowhile (exp_trans' lst e, stm_trans' lst i)
  | Proc (f, es) -> Clight.Scall (None, Clight.Evar (idn lst f, Tvoid), 
                                  List.map (exp_trans' lst) es)
  | If (e, i1, i2) -> 
      Clight.Sifthenelse (exp_trans' lst e, stm_trans' lst i1, 
                          begin match i2 with
                            | None -> Clight.Sskip
                            | Some i -> stm_trans' lst i end)


and switch_aux lst s o =
  match s with
    | [] -> begin match o with
        | None -> Clight.LSdefault 
            (Clight.Scall (None, Clight.Evar (idn lst "abort", Tvoid), []))
        | Some o -> Clight.LSdefault (stm_trans' lst o)
      end
    | (str, i) :: t ->
        Clight.LScase (num str, stm_trans' lst i, switch_aux lst t o)
;;


let type_of_var = function

  | "S" | "L" | "mmod" | "F" | "I" | "A" | "R" | "x" | "y" | "X" | "U" | "W"
  | "shifter_carry_out" | "E" -> Tint (I8, Unsigned)
      
  | "n" | "d" | "m" | "s" | "dHi" | "dLo" | "imod" | "immed_8" | "rotate_imm"
  | "field_mask" | "shift_imm" | "sat_imm" | "rotate" | "cp_num"
  | "immedH" | "immedL" | "offset_8" | "shift" 
  | "opcode_1" | "opcode_2" | "CRn" | "CRm" -> Tint (I8, Unsigned)

  | "cond" -> Tint (I32, Signed)
  | "old_mode" | "mode" -> Tint (I32, Signed)
  | "accvalue" | "result" | "value" -> Tint (I32, Unsigned)
  | _ -> Tint (I32, Unsigned)

module G = struct

  type typ = Csyntax.coq_type;;

  let global_type = type_of_var;;

  let local_type s _ = type_of_var s

  let rec explicit_annot_type ty _ = typ_trans ty
  
  let case_type = Tint (I32, Unsigned);;

end;;

module V = Ast.Make(G);;

let add_index l =
  let rec aux n = function
    | [] -> []
    | (_, b) :: t -> 
        Coq_pair (pos_of_Z (Camlcoq.z_of_camlint (Int32.of_int n)), b) 
        :: aux (n+1) t
  in aux 0 l;;

let fn_trans p = 
  let gs, ls = V.vars p.pinst in
  let ls_id = add_index ls and gs_id = add_index gs in
  {fn_return = Tvoid;
   fn_params = gs_id;
   fn_vars = ls_id;
   Clight.fn_temps = [];
   fn_body = stm_trans' ls (p.pinst)};;
 
