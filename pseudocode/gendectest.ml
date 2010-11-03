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
open Validity;;
open Flatten;;
open Syntaxtype;;

(*****************************************************************************)
(* binary tests generation*)
(*****************************************************************************)

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

(*mask build by the bits from position p1 to p2*)
let mask p1 p2 =
  let rec aux p n =
    if (n=0) then
      Int32.shift_left Int32.one p
    else
      Int32.add (Int32.shift_left Int32.one p) (aux (p+1) (n-1))
  in aux p2 (p1-p2)
;;

(*get bits value form position p1 to p2*)
let get_bits p1 p2 w =
  Int32.shift_right (Int32.logand (mask p1 p2) w) p2;;

(*get the bits value by the name of parameter*)
let get_bits_by_name s ps w =
  let aux (s',p1,p2) w =
    if (s' = s) then get_bits p1 p2 w
    else Int32.zero
  in Int32.to_int (List.fold_right aux ps w)
;;

(*return the position p1 and p2 of parameter s*)
let get_pos s ps =
  let aux s (s', p1, p2) =
    if s = s' then [p1; p2]
    else []
  in List.map (aux s) ps
;;

(*operation on bitwise*)
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
	    | "LDRD" | "STRD" -> [NotLR "Rd"; NotPC "Rd"; IsEven "Rd"]
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
	    | "USAT"|"USAT16"|"UXTAB"|"UXTAB16"|"UXTAH"|"UXTB"|"UXTB16"|"UXTH" -> [NotPC "Rd"; NotPC "Rm"]
	    | _ -> []
	  end
  in aux p.fmode 
;;

(*a serie of bits whose value can't be v*)
let notv s lv (s', p1, p2) w =
  if (s' = s) then
    let m = upper_bound p1 p2 in
    let lst = Array.to_list (Array.init m (fun i -> i)) in
    let lst' = List.fold_right (fun v -> List.filter ((!=) v)) lv lst in
    let r = Random.int (List.length lst') in
      insert_bits (Int32.of_int (List.nth lst' r)) p2 w
  else w;;

(*NotPC*)
let notpc s params w = 
  notv s [15] params w;;

(*NotLR*)
let notlr s params w = 
  notv s [14] params w;;

(*two parameters that can't have the same value*)
let notsame s1 s2 lst_v w =
  let r2 = Random.int 16 in
  let aux (s2', _, p22) w =
    if (s2' = s2) then 
      let w1 = insert_bits (Int32.of_int r2) p22 w in
	w1
    else w
  in
    List.fold_right (notv s1 [r2]) lst_v (List.fold_right aux lst_v w)
;;

(*bits can't be zero*)
let notzero s (s', p1, p2) w =
  notv s [0] (s', p1, p2) w;;

let isodd (_,p1,p2) =
  let aux p1 p2 lst =
    let m = upper_bound p1 p2 in
    let l = Array.to_list (Array.init m (fun i -> i)) in
      List.fold_right (fun i j -> if (i mod 2) != 0 then j @ [i] else j) l lst
  in aux p1 p2 []
;;

(*value can't be odd*)
let iseven s params w =
  notv s (isodd params) params w;;

(*main function to generate instructions*)
let gen_tests_bin ps =
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
      | NotV (s, i) -> (List.fold_right (notv s [i]) (parameters_of ps.fdec) w)
      | NotSame (s1, s2) -> ((notsame s1 s2) (parameters_of ps.fdec) w)
      | NotZero s -> (List.fold_right (notzero s) (parameters_of ps.fdec) w)
      | NoWritebackDest -> (insert_bits Int32.zero 21 (gen (NotSame ("Rd", "Rn")) w))
      | NotLSL0 -> gen (Or ([NotZero "shift"], [NotZero "shift_imm"])) w
      | Not2lowRegs -> w
      | BLXbit0 -> w
      | NotZero2 _ -> w
      | IsEven s -> (List.fold_right (iseven s) (parameters_of ps.fdec) w)
      | OtherVC _ -> w 
  in match restrict ps with
    | [] -> vparams
    | r -> List.fold_right gen r vparams;;


let consts ps w =
  let rec aux1 res lst =
    let params = parameters_of ps.fdec in
    let bnames s p = if ((fun (s',_,_) -> s') p) = s then true else false
    in
      match res with 
	| NotPC s -> [(s, [15])]
	| NotLR s -> [(s, [14])]
	| NotV (s, i) -> [(s, [i])]
	| NotSame (s1, s2) -> [(s1, [])] @ [(s2, [get_bits_by_name s1 params w])]
	| NotZero s -> [(s, [0])]
	| NoWritebackDest -> (aux1 (NotSame ("Rd","Rn")) lst) @ [("W", [1])]
	| NotLSL0 -> []
	| Not2lowRegs -> []
	| BLXbit0 -> []
	| NotZero2 _ -> []
	| IsEven s -> [(s, isodd (List.find (bnames s) params))]
	| OtherVC _ -> []
	| Or (lv1, lv2) -> List.fold_right aux1 lv1 (List.fold_right aux1 lv2 lst)
  in 
    List.fold_right aux1 (restrict ps) []
;;

(*****************************************************************************)
(*build a list to store the parameters and their values*)
(*****************************************************************************)

let add_R ps =
  let aux (s, p1, p2) =
    match s with
      | ("d"|"n"|"m"|"s"|"dLo"|"dHi") as s' -> (("R"^s'), p1, p2)
      | _ -> (s, p1, p2)
  in 
    List.map aux ps
;;

(*mark each parameter with their constraints*)
let mark_params ps =
  let params = add_R (parameters_of ps.fdec) in
  let oparams = 
    let ar = Array.init (List.length params) 
      (fun i -> (List.nth params i, [None]))
    in Array.to_list ar
  in
  let is_s s (s',_,_) = (=) s s' 
  in
  let mark_ps s constr ops = 
    List.map (fun (p,c) -> 
		if (is_s s p) then (p, c@[Some constr]) else (p, c)) ops
  in 
  let aux restr ops =
    match restr with
      | NotPC s -> mark_ps s "PC" ops
      | NotLR s -> mark_ps s "LR" ops
      | NotV (s, i) -> mark_ps s (string_of_int i) ops
      | NotSame (s1, s2) -> mark_ps s2 "NotSame2" (mark_ps s1 "NotSame1" ops)
      | NotZero s -> mark_ps s "0" ops
      | NoWritebackDest -> mark_ps "W" "0" ops
      | NotLSL0|Not2lowRegs|BLXbit0|NotZero2 _
      | IsEven _|OtherVC _|Or _ -> mark_ps "" "" ops
  in 
    match (restrict ps) with
      | [] -> oparams
      | lst -> List.fold_right aux lst oparams
;;


(*associate the parameter with a list of valid values*)
let build_lv ops =
  let aux (p, lconstr) =
    let aux1 constr =
      match constr with
	| Some optstr -> 
	    begin match optstr with
	      | "PC" -> [15]
	      | "LR" -> [14]
	      | "0" -> [0]
	      | _ -> []
	    end
	| None -> []
    in (p,List.flatten (List.map aux1 lconstr))
  in List.map aux ops
;;

let other_constr ops =
  let aux (p, c) =
    match p with
      | ("cond",_,_) -> (p,c@[15])
      | _ -> (p,c)
  in List.map aux ops

let valid_lst ops =
  let aux ((s', p1, p2), lv) =
    let m = upper_bound p1 p2 in
    let length = 
      if m> 0 && m<Sys.max_array_length
      then m else 1 in
    let lst = Array.to_list (Array.init length (fun i -> i)) in
    let lst' = List.fold_right (fun v -> List.filter ((!=) v)) lv lst in
      ((s',p1,p2),lst')
  in List.map aux (other_constr (build_lv ops))
;;

(*
let print_lst b ps =
  let aux b ((s,_,_),lst) =
    bprintf b "%s" s;
    (list " " int) b lst
  in 
    (list "" aux) b (valid_lst (mark_params ps))
;;*)


(*****************************************************************************)
(*assembly tests generation*)
(*****************************************************************************)

(*encoding condition*)
let cond v =
  match v with
    | 0 -> "EQ"
    | 1 -> "NE"
    | 2 -> "CS"
    | 3 -> "CC"
    | 4 -> "MI"
    | 5 -> "PL"
    | 6 -> "VS"
    | 7 -> "VC"
    | 8 -> "HI"
    | 9 -> "LS"
    | 10 -> "GE"
    | 11 -> "LT"
    | 12 -> "GT"
    | 13 -> "LE"
    | 14 -> "AL"
    | i -> string_of_int i

(*print registers by name*)
let reg r =
  match r with
    | 15 -> "PC"
    | 14 -> "LR"
    | 13 -> "SP"
    | 12 -> "IP"
    | 11 -> "FP"
    | 10 -> "LS" 
    | i -> "R"^string_of_int i

(*encoding of other parameters*)
let xy xy =
  match xy with
    | 0 -> "B"
    | 1 -> "T"
    | _ -> ""

let effect imod =
  match imod with
    | 0b10 -> "IE"
    | 0b11 -> "ID"
    | _ -> ""

let iflags a i f =
  match a, i, f with
    | 0, 0, 1 -> "f"
    | 0, 1, 0 -> "i"
    | 0, 1, 1 -> "if"
    | 1, 0, 0 -> "a"
    | 1, 0, 1 -> "af"
    | 1, 1, 0 -> "ai"
    | 1, 1, 1 -> "aif"
    | _ -> ""

let rotation rot =
  match rot with
    | 0b00 -> "Omitted"
    | 0b01 -> "ROR #8"
    | 0b10 -> "ROR #16"
    | 0b11 -> "ROR #32"
    | _ -> ""

(*get the vaule from the value table by the name of parameter*)
let get_v s lst = 
  (fun l -> 
     if l = [] then 0
     else (fun ((_,_,_),vs) -> List.nth vs (Random.int (List.length vs)))
       (List.nth l (Random.int (List.length l)))) 
    (List.filter (fun p -> (fun ((s',_,_), _) -> s') p =s) lst)
;;

(*main function to generate the instructions in assembly code*)
let asm_insts b ps =
  let aux b tk lst =
    match tk with
      | Const s -> bprintf b "%s" s
      | OptParam (s1, Some s2) -> 
	  begin match s2 with
	    | "cond" as s -> bprintf b "%s%s" s1 (cond (get_v s lst))
	    | "rotation" -> 
		bprintf b "%s%s" s1 (rotation (get_v "rotate" lst))
	    | "register_list"
	    | _ -> bprintf b "%s%d" s1 (get_v s2 lst)
	  end 
      | OptParam (s, None) -> 
	  if (get_v s lst = 1) then bprintf b "%s" s
	  else bprintf b ""
      | Param s -> 
	  begin match s with
	    | ("Rd"|"Rn"|"Rs"|"Rm"|"Rdhi"|"Rdlo") as s -> 
		bprintf b "%s" (reg (get_v s lst))
	    | ("x"|"y") as s -> bprintf b "%s" (xy (get_v s lst))
	    | "iflags" -> 
		bprintf b "%s" (iflags (get_v "A" lst) (get_v "I" lst) 
				  (get_v "F" lst))
	    | "effect" -> bprintf b "%s" (effect (get_v "imod" lst))
	    | _ -> bprintf b "%d" (get_v s lst)
	  end 
      | PlusMinus -> bprintf b "+/-"
  in let rec aux2 b var lst =
      match var with
	| [] -> bprintf b ""
	| tk::tks -> aux b tk lst; aux2 b tks lst
  in let rec aux3 b syn lst =
      match syn with
	| [] -> bprintf b ""
	| v::vs -> aux2 b v lst; bprintf b "\n"; aux3 b vs lst
  in aux3 b ps.fsyntax (valid_lst (mark_params ps))
;;

(*****************************************************************************)
(*output binary tests*)
(*****************************************************************************)

let bin_insts out fs =
  (*for i = 0 to 10 do*)
    output_word out (gen_tests_bin fs)
  (*done*)
;;

let gen_bin_test out pcs ss decs seed =
  set_binary_mode_out out true;
  Random.init seed;
  let fs: fprog list = List.filter is_arm (flatten pcs ss decs) in
    List.iter (bin_insts out) (List.rev fs)
;;

(*****************************************************************************)
(*output assembly tests*)
(*****************************************************************************)

let gen_asm_test bn pcs ss decs =
  let fs: fprog list = List.filter is_arm (flatten pcs ss decs) in
  let b = Buffer.create 100000 in
    (list "" asm_insts) b (List.rev fs);
    let outh = open_out (bn^".asm") in
      Buffer.output_buffer outh b; close_out outh;
;;
