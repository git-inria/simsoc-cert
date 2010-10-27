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

(*Set the seed of the random generator
let init = Random.init 1
;;*)

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

(*insert bits from position p*)
let insert_bits i p w =
  let is = Int32.shift_left i p in
    Int32.logor is w;;

type bitwise_change =
  | Insert_bits of int *int
  | No_change
;;

(*Generate bits randomly*)
(*let gen_bin pc =
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
let upper_bound p1 p2 =
  Int32.to_int (Int32.shift_left Int32.one (p1-p2+1))
;;

(*add constraint to instructions by addressing mode and name*)
let restrict p =
  let aux fmode =
    match fmode with
      | Some ("M1_LSRReg"|"M1_LSLReg"|"M1_ASRReg"|"M1_RRReg") -> 
	  [NotPC "Rd"; NotPC "Rm"; NotPC "Rn"; NotPC "Rs"]
      | Some ("M2_RegOff"|"M2_ScRegOff"|"M3_RegOff") -> 
	  [NotPC "Rm"]
      | Some ("M2_Imm_preInd"|"M2_Imm_postInd"|"M3_Imm_preInd"|"M3_Imm_postInd"|"M5_Imm_preInd") -> 
	  [NotPC "Rn"]
      | Some ("M2_Reg_preInd"|"M2_ScReg_preInd"|"M2_Reg_postInd"|"M2_Sc_Reg_postInd"|"M3_Reg_preInd"|"M3_Reg_postInd") -> 
	  [NotPC "Rm"; NotPC "Rn"; NotSame ("Rn", "Rm")]
      | Some ("M4_IA"|"M5_IB"|"M5_DA"|"M5_DB") -> [NotV ("S", 0b1); NotZero "register_list"]
      | Some "M5_U" -> [NotV ("U", 0b0)]
      | Some _ | None ->
	  begin match p.finstr with
	    | "ADC"|"ADD"|"AND" -> [NotPC "Rd"]
	    | "CLZ" -> [NotPC "Rm"; NotPC "Rd"]
	    | "CPS" ->
		[Or ([NotV ("imod", 0b00); NotV("mmod", 0b0)], 
		    [Or ([NotV ("imod",0b01); NotV ("mmod", 0b0)], 
			[NotV ("imod", 0b01); NotV ("mmod", 0b1)])])]
	    | "LDM1"|"LDM2"|"STM1"|"STM2" -> [NotPC "Rn"; NotZero "register_list"]
	    | "LDM3"|"LDRB" -> [NotPC "Rn"]
	    | "LDR"|"STR"|"STRB" -> [NoWritebackDest]
	    | "LDRD" | "STRD" -> [NotLR "Rd"; IsEven "Rd"]
	    | "LDRBT" -> [NotPC "Rn"; NotSame ("Rd", "Rn")]
	    | "LDREX" -> [NotPC "Rn"; NotPC "Rd"]
	    | "LDRH"|"LDRSB"|"LDRSH"|"STRH" -> [NotPC "Rd"; NoWritebackDest]
	    | "LDRT"|"STRBT" -> [NotPC "Rd"; NotSame ("Rd", "Rn")]
	    | "MCR"|"MCRR"|"MRS"-> [NotPC "Rd"]
	    | "MLA"|"SMLAxy"|"SMLAWy"|"SMLSD"|"SMMLS"  -> 
		[NotPC "Rd"; NotPC "Rm"; NotPC "Rs"; NotPC "Rn"]
	    | "MRRC" -> [NotSame ("Rd", "Rn"); NotPC "Rd"; NotPC "Rn"]
	    | "MUL"  -> [NotPC "Rd"; NotPC "Rs"; NotPC "Rm"]
	    | "PKHBT"|"PKHTB"|"QADD"|"QADD8"|"QADD16"|"QADDSUBX"|"QDADD"|"QDSUB"|"QSUB"|"QSUB16"|"QSUB8"|"QSUBADDX"|"SADD16"|"SADD8"|"SADDSUBX"|"SEL"|"SHADD16"|"SHADD8"|"SHADDSUBX"|"SHSUB16"|"SHSUB8"|"SHSUBADDX"|"SSUB16"|"SSUB8"|"SSUBADDX"
		-> [NotPC "Rn"; NotPC "Rd"; NotPC "Rm"]
	    | "REV"|"REV16"|"REVSH"|"SSAT"|"SSAT16"|"SXTAB"|"SXTAB16"|"SXTAH"|"SXTB"|"SXTB16"|"SXTH"-> [NotPC "Rd"; NotPC "Rm"]
	    | "RFE" -> [NotPC "Rn"]
	    | "SMLAD" -> [NotPC "Rd"; NotPC "Rm"; NotPC "Rs"]
	    | "SMLAL"-> [NotPC "RdHi"; NotPC "RdLo"; NotPC "Rs"; NotPC "Rm"]
	    | "SMLALxy"|"SMLALD"|"SMLSLD"|"SMULL"|"UMAAD"|"UMLAL"|"UMULL"-> [NotPC "RdHi"; NotPC "RdLo"; NotPC "Rs"; NotPC "Rm"; NotSame ("Rd","Rn")]
	    | "SMMUL"|"SMUAD"|"SMULxy"|"SMULWy"|"SMUSD"|"USAD8"|"USADA8" -> [NotPC "Rd"; NotPC "Rs"; NotPC "Rm"]
	    | "STREX" -> [NotPC "Rn"; NotPC "Rd"; NotPC "Rm"; NotSame ("Rd","Rm"); NotSame ("Rd","Rn")]
	    | "STRT"-> [NotSame ("Rd","Rn")]
	    | "SWP"|"SWPB" -> [NotPC "Rn"; NotPC "Rd" ;NotPC "Rm"; NotSame ("Rd","Rm"); NotSame ("Rd","Rn")]
	    | "UADD16"|"UADD8"|"UADDSUBX"|"UHADD16"|"UHADD8"|"UHADDSUBX"|"UHSUB16"|"UHSUB8"|"UHSUBADDX"|"UQADD16"|"UQADD8"|"UQADDSUBX"|"UQSUB16"|"UQSUB8"|"UQSUBADDX"|"USUB16"|"USUB8"|"USUBADDX" -> [NotPC "Rn"; NotPC "Rd"; NotPC "Rm"]
	    | "USAT"|"USAT16"|"UXTAB"|"UXTAB16"|"UXTAH"|"UXTB"|"UXTB16"|"UXT H" -> [NotPC "Rd"; NotPC "Rm"]
	    | _ -> []
	  end
  in aux p.fmode 
;;

(*a serie of bits whose value can't be i*)
let notv s v (s', p1, p2) w =
  if (s' = s) then
    let m = upper_bound p1 p2 in
    let lst = Array.to_list (Array.init m (fun i -> i)) in
    let lst' = List.filter ((!=) v) lst in
    let r = Random.int (List.length lst') in
      insert_bits (Int32.of_int (List.nth lst' r)) p2 w
  else w;;

(*NotPC*)
let notpc s params w = 
  notv s 15 params w;;

(*NotLR*)
let notlr s params w = 
  notv s 14 params w;;

(*two parameters that can't have the same value*)
let notsame s1 s2 lst_v w =
  let r2 = Random.int 16 in
  let aux (s2', _, p22) w =
    if (s2' = s2) then 
      let w1 = insert_bits (Int32.of_int r2) p22 w in
	w1
    else w
  in
    List.fold_right (notv s1 r2) lst_v (List.fold_right aux lst_v w)
;;

(*bits can't be zero*)
let notzero s (s', p1, p2) w =
  notv s 0 (s', p1, p2) w;;

(*value can't be odd*)
let iseven s (s', p1, p2) w =
  if (s' = s) then 
    let is = (Random.int (upper_bound p1 p2)) in
      insert_bits (Int32.of_int ((is/2)*2)) p2 w
  else w;;

(*main function to generate instructions*)
let gen_tests ps =
  let fix_bits dec =
    match dec with
      | (Shouldbe b, p) -> Insert_bits ((if b then 0b1 else 0b0),p)
      | (Value i, p) -> Insert_bits ((if i then 0b1 else 0b0), p)
      | ((Range _ | Param1 _ | Param1s _ | Nothing), _) -> No_change
  in
  let random_bits ps =
    match ps with
      | (("Rn"|"Rm"|"Rs"|"Rd"|"RdLo"|"RdHi"),_, p2) -> 
	  Insert_bits (Random.int 16, p2)
      | ("cond",_, p2) -> Insert_bits (Random.int 15, p2)
      | (_, p1, p2) -> 
	  Insert_bits (Random.int (upper_bound p1 p2), p2)    
  in 
  let no_restrict_bits clst params =
    let aux (s,p1,p2) =
      if (List.exists ((=)s) clst) then 
	No_change 
      else 
	random_bits (s,p1,p2)
    in List.map aux params
  in
  let proc vs w =
    match vs with
      | Insert_bits (i, p) -> insert_bits (Int32.of_int i) p w
      | No_change -> w
  in 
  let pos dec =
    let ar = Array.create (Array.length dec) (Nothing, 0) in
      for i = 0 to Array.length dec - 1 do
	ar.(i) <- (dec.(i), i)
      done;
    ar
  in
  let rem ps =
    let rec aux res lst =
      match res with
	| NotPC s| NotLR s| NotV (s,_)| NotZero s| IsEven s-> lst @ [s]
	| NotSame (s1,s2)| NotZero2 (s1,s2)-> lst @ [s1; s2]
	| NoWritebackDest-> lst @ ["W"]
	| NotLSL0| Not2lowRegs| BLXbit0| OtherVC _ -> lst
	| Or(l1,_)-> List.fold_right aux l1 lst
    in List.fold_right aux (restrict ps) []
  in
  let vparams =
    Int32.logor (Array.fold_right proc (Array.map fix_bits (pos ps.fdec)) Int32.zero)
      (List.fold_right proc (no_restrict_bits (rem ps) (parameters_of ps.fdec)) Int32.zero)
  in
  let rec gen res w = 
    match res with
      | Or (lv1, lv2) ->
	  if Random.bool() then (List.fold_right gen lv1 w) else (List.fold_right gen lv2 w)
      | NotPC s -> (List.fold_right (notpc s) (parameters_of ps.fdec) w)
      | NotLR s -> (List.fold_right (notlr s) (parameters_of ps.fdec) w)
      | NotV (s, i) -> (List.fold_right (notv s i) (parameters_of ps.fdec) w)
      | NotSame (s1, s2) -> ((notsame s1 s2) (parameters_of ps.fdec) w)
      | NotZero s -> (List.fold_right (notzero s) (parameters_of ps.fdec) w)
      | NoWritebackDest -> (insert_bits Int32.zero 21 (gen (NotSame ("Rd", "Rn")) w))
      | NotLSL0 -> w
      | Not2lowRegs -> w
      | BLXbit0 -> w
      | NotZero2 _ -> w
      | IsEven s -> (List.fold_right (iseven s) (parameters_of ps.fdec) w)
      | OtherVC _ -> w
  in match restrict ps with
    | [] -> vparams
    | r -> List.fold_right gen r vparams;;

let bin_insts out fs =
  (*for i = 0 to 10 do*)
    output_word out (gen_tests fs)
  (*done*)
;;

let gen_test out pcs ss decs seed =
  set_binary_mode_out out true;
  Random.init seed;
  let fs: fprog list = List.filter is_arm (flatten pcs ss decs) in
    List.iter (bin_insts out) fs;;
