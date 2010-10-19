(**
SimSoC-Cert, a library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Generate the binary instruction for SimSoC decoder.
*)

open Ast;;
open Printf;;
open Util;;     (* for the "list" function *)
open Codetype;; (* from the directory "refARMparsing" *)
open Gencoqdec;;
open Dec;;
open Validity;;
open Flatten;;

(*Set the seed of the random generator*)
let init = Random.init 1
;;

(* output a 32 bits word in little-endian *)
let output_word out (word: int32) =
  output_byte out (Int32.to_int word);
  output_byte out (Int32.to_int (Int32.shift_right_logical word 8));
  output_byte out (Int32.to_int (Int32.shift_right_logical word 16));
  output_byte out (Int32.to_int (Int32.shift_right_logical word 24));;

(* add a bit on the right of 'w', e.g.: push_bit true 0b101 = 0b1011 *)
let push_bit (b: bool) (w: int32) =
  let w' = Int32.shift_left w 1 in
    if b then Int32.succ w' else w'

let push_bits (x: bool array) (y: int32) =
  let lst = Array.to_list x in
    List.fold_right push_bit lst y;; 

let insert_bit (b: int32) (p: int) (w: int32) =
  let i = Int32.shift_left b p in
    Int32.logor i w;;

(*insert bits at from position p*)
let insert_bits i p w =
  let is = Int32.shift_left i p in
    Int32.logor is w;;

type vcon =
  | Insert_bits of int *int
  | Insert_bit of bool * int
  | No_change
;;

type vconstraint =
  | NotPC of string   (* the string must contains the name of parameter *)
  | NotLR of string (* the string must contains the name of parameter *)
  | IsEven of string   (* parameter that should contain an even value *)
  | NoWritebackDest    (* no write-back with Rd==Rn *)
  | NotSame of string * string (* R<a> <> R<b> *)
  (*| NotLSL0            (* to distinguished between (equivalent?) mode cases *)*)
  | OtherVC of exp     (* Other validy constraints described by a boolean
   * expression *)
  | NotV of string * bool
  | NotVs of string * int
  | And of vconstraint * vconstraint
  | NotZero of string
  | Or of vconstraint * vconstraint
  | NoRestrict
;;

(*
(*Generate bits randomly*)
let gen_bin pc =
  let aux ls w =
    match ls with
      | Value s -> push_bit s w
      | Shouldbe s -> push_bit s w
      | Param1 _ | Param1s _ -> push_bit (Random.bool ()) w
      | Range _ -> push_bit (Random.bool ()) w
      | Nothing -> raise (Failure "unexpected case")
  in Array.fold_right aux pc Int32.zero;;

let bin_inst out ps =
  let md = add_mode (name ps) in
    match md with
      | DecInst -> (*output_word out (gen_bin ls)*)
      | DecEncoding -> ()
      | DecMode _ -> ();;

let gen_tests out _ dec =
  set_binary_mode_out out true;
  List.iter (bin_inst out) dec;;
*)

(*the upper bound of random generation for parameter (s,p1 p2) in general case*)
let max_v p1 p2 =
  Int32.to_int (Int32.shift_left Int32.one (p1-p2));;

let restrict p =
let aux fmode =
  match fmode with
    | Some ("M1_LSRReg"|"M1_LSLReg"|"M1_ASRReg"|"M1_RRReg") -> 
	And (NotPC "Rd", And (NotPC "Rm", And (NotPC "Rn", NotPC "Rs")))
    | Some ("M2_RegOff"|"M2_ScRegOff"|"M3_RegOff") -> 
	NotPC "m"
    | Some ("M2_Imm_preInd"|"M2_Imm_postInd"|"M3_Imm_preInd"|"M3_Imm_postInd"|"M5_Imm_preInd") -> 
	NotPC "Rn"
    | Some ("M2_Reg_preInd"|"M2_ScReg_preInd"|"M2_Reg_postInd"|"M2_Sc_Reg_postInd"|"M3_Reg_preInd"|"M3_Reg_postInd") -> 
	And (NotPC "Rm", And (NotPC "Rn", NotSame ("Rn", "Rm")))
    | Some ("M4_IA"|"M5_IB"|"M5_DA"|"M5_DB") -> And (NotV ("S", true), NotZero "register_list")
    | Some "M5_U" -> NotV ("U", false)
    | Some _ | None ->
	begin match p.finstr with
	  | "ADC"|"ADD"|"AND" -> NotPC "Rd"
	  | "CLZ" -> And (NotPC "Rm", NotPC "Rd")
	  | "CPS" ->
	      Or (And (NotVs ("imod", 0b00), NotV("mmod", false)), 
		  Or (And (NotVs ("imod",0b01), NotV ("mmod", false)), 
		      And (NotVs ("imod", 0b01), NotV ("mmod", true))))
	  | "LDM1"|"LDM2"|"STM1"|"STM2" -> And (NotPC "Rn", NotZero "register_list")
	  | "LDM3"|"LDRB" -> NotPC "Rn"
	  | "LDR"|"STR"|"STRB" -> NoWritebackDest
	  | "LDRD" | "STRD" -> And (NotLR "Rd", IsEven "Rd")
	  | "LDRBT" -> And (NotPC "Rn", NotSame ("Rd", "Rn"))
	  | "LDREX" -> And (NotPC "Rn", NotPC "Rd")
	  | "LDRH"|"LDRSB"|"LDRSH"|"STRH" -> And (NotPC "Rd", NoWritebackDest)
	  | "LDRT"|"STRBT" -> And (NotPC "Rd", NotSame ("Rd", "Rn"))
	  | "MCR"|"MCRR"|"MRS"-> NotPC "Rd"
	  | "MLA"|"SMLAxy"|"SMLAWy"|"SMLSD"|"SMMLS"  -> 
	       And (NotPC "Rd", And (NotPC "Rm", And (NotPC "Rs", NotPC "Rn")))
	  | "MRRC" -> And (NotSame ("Rd", "Rn"), And (NotPC "Rd", NotPC "Rn"))
	  | "MUL"  -> And (NotPC "Rd", And (NotPC "Rs", NotPC "Rm"))
	  | "PKHBT"|"PKHTB"|"QADD"|"QADD8"|"QADD16"|"QADDSUBX"|"QDADD"|"QDSUB"|"QSUB"|"QSUB16"|"QSUB8"|"QSUBADDX"|"SADD16"|"SADD8"|"SADDSUBX"|"SEL"|"SHADD16"|"SHADD8"|"SHADDSUBX"|"SHSUB16"|"SHSUB8"|"SHSUBADDX"|"SSUB16"|"SSUB8"|"SSUBADDX"
	-> And (NotPC "Rn", And (NotPC "Rd", NotPC "Rm"))
	  | "REV"|"REV16"|"REVSH"|"SSAT"|"SSAT16"|"SXTAB"|"SXTAB16"|"SXTAH"|"SXTB"|"SXTB16"|"SXTH"-> And (NotPC "Rd", NotPC "Rm")
	  | "RFE" -> NotPC "Rn"
	  | "SMLAD" -> And (NotPC "Rd", And (NotPC "Rm", NotPC "Rs"))
	  | "SMLAL"-> And (NotPC "RdHi", And (NotPC "RdLo", And (NotPC "Rs", NotPC "Rm")))
	  | "SMLALxy"|"SMLALD"|"SMLSLD"|"SMULL"|"UMAAD"|"UMLAL"|"UMULL"-> And (NotPC "RdHi", And (NotPC "RdLo", And (NotPC "Rs", And (NotPC "Rm", NotSame ("Rd","Rn")))))
	  | "SMMUL"|"SMUAD"|"SMULxy"|"SMULWy"|"SMUSD"|"USAD8"|"USADA8" -> And (NotPC "Rd", And (NotPC "Rs", NotPC "Rm"))
	  | "STREX" -> And (NotPC "Rn", And (NotPC "Rd", And (NotPC "Rm", And (NotSame ("Rd","Rm"), NotSame ("Rd","Rn")))))
	  | "STRT"-> NotSame ("Rd","Rn")
	  | "SWP"|"SWPB" -> And (NotPC "Rn", And (NotPC "Rd", And (NotPC "Rm", And (NotSame ("Rd","Rm"), NotSame ("Rd","Rn")))))
	  | "UADD16"|"UADD8"|"UADDSUBX"|"UHADD16"|"UHADD8"|"UHADDSUBX"|"UHSUB16"|"UHSUB8"|"UHSUBADDX"|"UQADD16"|"UQADD8"|"UQADDSUBX"|"UQSUB16"|"UQSUB8"|"UQSUBADDX"|"USUB16"|"USUB8"|"USUBADDX" -> And (NotPC "Rn", And (NotPC "Rd", NotPC "Rm"))
	  | "USAT"|"USAT16"|"UXTAB"|"UXTAB16"|"UXTAH"|"UXTB"|"UXTB16"|"UXT H" -> And (NotPC "d", NotPC "Rm")
	  | _ -> NoRestrict
	end
in aux p.fmode 
;;


let notpc s (s', _, p2) w = 
  if (s' = s) then insert_bits (Int32.of_int (Random.int 15)) p2 w
  else w;;

let notlr s (s', _, p2) w = 
  if (s' = s) then insert_bits (Int32.of_int (Random.int 14)) p2 w
  else w;;

let notv s b (s', _, p2)  w =
  if (s' = s) then insert_bit (if (not b) then Int32.one else Int32.zero) p2 w
  else w;;

let notvs s i (s', p1, p2) w =
  if (s' = s) then
    let r = Random.int (max_v p1 p2) in
      insert_bits (Int32.of_int (if (r = i) then (r+ 1) else r)) p2 w
  else w;;

let notsame s1 s2 params w =
  match params with
    | (s1', _, p12) -> 
	if (s1' = s1) then 
	  match params with
	    | (s2', _, p22) -> 
		if (s2' = s2) then
		  let r1 = Random.int 16 in
		  let r2 = Random.int 15 in
		    insert_bits (Int32.of_int r1) p12 
		      (insert_bits (Int32.of_int (if (r2 = r1) then (r2+ 1) else r2)) p22 w)
		else w
	else w
;;

let notzero s (s', p1, p2) w =
  if (s' = s) then 
    let is = (Random.int (max_v p1 p2)) in
      insert_bits (Int32.of_int (if (is = 0) then (is+ 1) else is)) p2 w
  else w;;

let iseven s (s', p1, p2) w =
  if (s' = s) then 
    let is = (Random.int (max_v p1 p2)) in
      insert_bits (Int32.of_int ((is/2)*2)) p2 w
  else w;;

let gen_tests ps =
  let fix_bits dec =
    match dec with
      | (Shouldbe b, p) -> Insert_bit (b,p)
      | (Value i, p) -> Insert_bit (i, p)
      | ((Range _ | Param1 _ | Param1s _ | Nothing), _) -> No_change
  in
  let random_bits ps =
    match ps with
      | (("n"|"m"|"s"|"d"|"dLo"|"dHi"),_, p2) -> 
	  Insert_bits (Random.int 16, p2)
      | (("cond"),_, p2) -> Insert_bits (Random.int 15, p2)
      | (_, p1, p2) -> 
	  Insert_bits (Random.int (max_v p1 p2), p2)  
  in let no_restrict_bits s (s', p1, p2) =
      if (s' = s) then
	No_change
      else Insert_bits (Random.int (max_v p1 p2), p2)
  in
  let proc vs w =
    match vs with
      | Insert_bits (i, p) -> insert_bits (Int32.of_int i) p w
      | Insert_bit (b, p) -> insert_bit (if b then Int32.one else Int32.zero) p w
      | No_change -> w
  in 
  let pos dec =
    let ar = Array.create (Array.length dec) (Nothing, 0) in
      for i = 0 to Array.length dec - 1 do
	ar.(i) <- (dec.(i), i)
      done;
    ar
  in
  let vparams s w1 =
    Int32.logor w1
      (Int32.logor (Array.fold_right proc (Array.map fix_bits (pos ps.fdec)) Int32.zero)
	 (List.fold_right proc (List.map (no_restrict_bits s) (parameters_of ps.fdec)) Int32.zero)) 
  in
  let rec gen res w = 
    match res with
      | Or (v1, v2) ->
	  if Random.bool() then (gen v1 w) else (gen v2 w)
      | And (v1, v2) -> gen v1 (gen v2 w)
      | NotPC s -> vparams s (List.fold_right (notpc s) (parameters_of ps.fdec) w)
      | NotLR s -> vparams s (List.fold_right (notlr s) (parameters_of ps.fdec) w)
      | NotV (s, b) -> vparams s(List.fold_right (notv s b)(parameters_of ps.fdec)  w)
      | NotVs (s, i) -> vparams s (List.fold_right (notvs s i) (parameters_of ps.fdec) w)
      | NotSame (s1, s2) -> vparams s2 (List.fold_right (notsame s1 s2) (parameters_of ps.fdec)  w)
      | NotZero s -> vparams s (List.fold_right (notzero s) (parameters_of ps.fdec) w)
      | NoWritebackDest -> vparams "W" (insert_bit Int32.zero 21 (gen (NotSame ("d", "n")) w))
      | NoRestrict -> 
	  Int32.logor (Array.fold_right proc (Array.map fix_bits (pos ps.fdec)) w)
	    (List.fold_right proc (List.map random_bits (parameters_of ps.fdec)) w)
      | IsEven s -> vparams s (List.fold_right (iseven s) (parameters_of ps.fdec) w)
      | OtherVC _ -> Int32.zero
  in match ps.finstr with
    | _ ->
	gen (restrict ps) Int32.zero
    (*| _ -> Int32.zero*)
;;

let bin_insts out fs =
  (*for i = 0 to 10 do*)
    output_word out (gen_tests fs)
  (*done*)
;;

let gen_test out pcs decs =
  set_binary_mode_out out true;
  let fs: fprog list = List.filter is_arm (flatten pcs decs) in
    List.iter (bin_insts out) fs;;
