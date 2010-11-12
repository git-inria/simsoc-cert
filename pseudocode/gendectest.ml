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

(* output a 32 bits word in little-endian *)
let output_word out (word: int32) =
  output_byte out (Int32.to_int word);
  output_byte out (Int32.to_int (Int32.shift_right_logical word 8));
  output_byte out (Int32.to_int (Int32.shift_right_logical word 16));
  output_byte out (Int32.to_int (Int32.shift_right_logical word 24));;


(*insert bits from position p*)
let insert_bits i p w =
  let is = Int32.shift_left i p in
    Int32.logor is w;;

(*mask build by the bits from position p1 to p2*)
let mask p1 p2 =
  let size = p1-p2+1 in (* number of bit in the mask *)
    if size=32 then Int32.minus_one
    else Int32.shift_left (Int32.sub (Int32.shift_left Int32.one size) Int32.one) p2
;;

let test_mask =
  let expected = Int32.of_int 0xf0 in
    if expected <> mask 7 4 then raise (Failure "mask is wrong"); ();;

(*get bits value form position p1 to p2*)
let get_bits p1 p2 w =
  Int32.shift_right (Int32.logand (mask p1 p2) w) p2;;

(*operation on bitwise*)
type bitwise_change =
  | Insert_bits of int *int
  | No_change
;;

(*add constraint to instructions by addressing mode and name*)
let restrict p =
  let mode_constraints fmode =
    match fmode with
      | Some ("M1_LSRReg"|"M1_LSLReg"|"M1_ASRReg"|"M1_RRReg") -> 
	  [NotPC "Rd"; NotPC "Rm"; NotPC "Rn"; NotPC "Rs"]
      | Some ("M1_Imm"|"M1_LSLImm"|"M1_ASRImm"|"M1_RRImm"|"M1_LSRImm") -> 
	  [NotLSL0]
      | Some ("M2_RegOff"|"M3_RegOff") -> 
	  [NotPC "Rm"]
      | Some ("M2_Imm_preInd"|"M2_Imm_postInd"|"M3_Imm_preInd"|
		  "M3_Imm_postInd"|"M5_Imm_preInd") -> 
	  [NotPC "Rn"]
      | Some "M2_ScReg_postInd" ->
	  [NotPC "Rm"; NotPC "Rn"; NotSame ("Rn", "Rm"); NotLSL0]
      | Some ("M2_Reg_preInd"|"M2_Reg_postInd"|
		  "M3_Reg_preInd"|"M3_Reg_postInd") -> 
	  [NotPC "Rm"; NotPC "Rn"; NotSame ("Rn", "Rm")]
      | Some "M2_ScReg_preInd" -> 
	  [NotPC "Rm"; NotPC "Rn"; NotSame ("Rn", "Rm"); NotLSL0]
      | Some "M2_ScRegOff" -> [NotPC "Rm"; NotLSL0]
      | Some ("M4_IA"|"M5_IB"|"M5_DA"|"M5_DB") ->
	  [NotV ("S", 0b1); NotZero "register_list"]
      | Some "M5_U" -> [NotV ("U", 0b0)]
      | Some _ | None -> []
  in
  let instr_constraints finstr =
    begin match finstr with
      | "ADC"|"ADD"|"AND" -> [NotPC "Rd"]
      | "CLZ" -> [NotPC "Rm"; NotPC "Rd"]
      | "CPS" ->
	  [Or ([NotV ("imod", 0b00); NotV("mmod", 0b0)], 
	       [Or ([NotV ("imod",0b01); NotV ("mmod", 0b0)], 
		    [NotV ("imod", 0b01); NotV ("mmod", 0b1)])])]
      | "LDM1"|"LDM2"|"STM1"|"STM2" -> [NotPC "Rn"; NotZero "register_list"]
      | "LDM3" -> [NotPC "Rn"]
      | "LDR"|"STR" -> [NoWritebackDest]
      | "LDRB" |"STRB" -> [NotPC "Rd"; NoWritebackDest]
      | "LDRD" | "STRD" -> [NotLR "Rd"; NotPC "Rd"; IsEven "Rd"]
      | "LDRBT" -> [NotPC "Rd"; NotSame ("Rd", "Rn")]
      | "LDREX" -> [NotPC "Rn"; NotPC "Rd"]
      | "LDRH"|"LDRSB"|"LDRSH"|"STRH" -> [NotPC "Rd"; NoWritebackDest]
      | "LDRT"|"STRBT" -> [NotPC "Rd"; NotSame ("Rd", "Rn")]
      | "MCR"|"MCRR"|"MRS"-> [NotPC "Rd"]
      | "MLA"|"SMLAxy"|"SMLAWy"|"SMLSD"|"SMMLS"  -> 
	  [NotPC "Rd"; NotPC "Rm"; NotPC "Rs"; NotPC "Rn"]
      | "MRRC" -> [NotSame ("Rd", "Rn"); NotPC "Rd"; NotPC "Rn"]
      | "MUL"  -> [NotPC "Rd"; NotPC "Rs"; NotPC "Rm"]
      | "PKHBT"|"PKHTB"|"QADD"|"QADD8"|"QADD16"|"QADDSUBX"|"QDADD"|"QDSUB"|"QSUB"
      |	"QSUB16"|"QSUB8"|"QSUBADDX"|"SADD16"|"SADD8"|"SADDSUBX"|"SEL"|"SHADD16"|"SHADD8"
      |"SHADDSUBX"|"SHSUB16"|"SHSUB8"|"SHSUBADDX"|"SSUB16"|"SSUB8"|"SSUBADDX"
	  -> [NotPC "Rn"; NotPC "Rd"; NotPC "Rm"]
      | "REV"|"REV16"|"REVSH"|"SSAT"|"SSAT16"|"SXTAB"
      |"SXTAB16"|"SXTAH"|"SXTB"|"SXTB16"|"SXTH"-> [NotPC "Rd"; NotPC "Rm"]
      | "RFE" -> [NotPC "Rn"]
      | "SMLAD"|"SMMLA" -> [NotPC "Rd"; NotPC "Rm"; NotPC "Rs"]
      | "SMLAL"-> [NotPC "RdHi"; NotPC "RdLo"; NotPC "Rs"; NotPC "Rm"]
      | "SMLALxy"|"SMLALD"|"SMLSLD"|"SMULL"|"UMAAD"|"UMLAL"|"UMULL"->
	  [NotPC "RdHi"; NotPC "RdLo"; NotPC "Rs"; NotPC "Rm"; NotSame ("Rd","Rn")]
      | "SMMUL"|"SMUAD"|"SMULxy"|"SMULWy"|"SMUSD"|"USAD8"|"USADA8" ->
	  [NotPC "Rd"; NotPC "Rs"; NotPC "Rm"]
      | "STREX" ->
	  [NotPC "Rn"; NotPC "Rd"; NotPC "Rm"; NotSame ("Rd","Rm"); NotSame ("Rd","Rn")]
      | "STRT"-> [NotSame ("Rd","Rn")]
      | "SWP"|"SWPB" ->
	  [NotPC "Rn"; NotPC "Rd" ;NotPC "Rm"; NotSame ("Rn","Rm"); NotSame ("Rd","Rn")]
      | "UADD16"|"UADD8"|"UADDSUBX"|"UHADD16"|"UHADD8"|"UHADDSUBX"|"UHSUB16"|"UHSUB8"
      |"UHSUBADDX"|"UQADD16"|"UQADD8"|"UQADDSUBX"|"UQSUB16"|"UQSUB8"|"UQSUBADDX"
      |"USUB16"|"USUB8"|"USUBADDX" -> [NotPC "Rn"; NotPC "Rd"; NotPC "Rm"]
      | "USAT"|"USAT16"|"UXTAB"|"UXTAB16"|"UXTAH"|"UXTB"|"UXTB16"|"UXTH" ->
	  [NotPC "Rd"; NotPC "Rm"]
      | _ -> []
    end
  in mode_constraints p.fmode @ instr_constraints p.finstr 
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
  let params: (string * int * int) list = add_R (parameters_of ps.fdec) in
  let oparams: ((string * int * int) * int list) list =
    List.map (fun p -> p, []) params
  in
  let is_s s (s',_,_) = s = s' 
  in
  let mark_ps (s:string) (constr: int list)
      (ops: ((string * int * int) * int list) list) = 
    List.map (fun (p,c) -> if (is_s s p) then (p, c @ constr) else (p, c)) ops in
  let isodd = (Array.to_list (Array.init 8 (fun i -> 2*i+1)))
  in
  let rec constraint_to_exclusion_list restr ops =
    match restr with
      | NotPC s -> mark_ps s [15] ops
      | NotLR s -> mark_ps s [14] ops
      | NotV (s, i) -> mark_ps s [i] ops
      | NotZero s -> mark_ps s [0] ops
      | NoWritebackDest ->
	  constraint_to_exclusion_list (Or ([NotV ("W", 1)], [NotSame ("Rd","Rn")])) ops
      | NotZero2 (s1, s2) -> 
	  constraint_to_exclusion_list (Or ([NotZero s1], [NotZero s2])) ops
      | Or (r1, r2) -> if Random.bool()
	then List.fold_right constraint_to_exclusion_list r1 ops
	else List.fold_right constraint_to_exclusion_list r2 ops
      | NotLSL0 -> mark_ps "shift_imm" [0] ops
      | IsEven s -> mark_ps s isodd ops
      | Not2lowRegs| BLXbit0 | OtherVC _ | NotSame _ -> ops
  in 
    List.fold_right constraint_to_exclusion_list (restrict ps) oparams
;;

(* condition has value from 0 to 14 
 * and mode has 7 values that has meaning *)
let other_constr ops =
  let md = [0b10000;0b10001;0b10010;0b10011;0b10111;0b11011;0b11111] in
  let not_mode = List.fold_right (fun m -> List.filter ((<>)m)) md
    (Array.to_list (Array.init 32 (fun i -> i))) in
  let aux (p, c) =
    match p with
      | ("cond",_,_) -> (p,c@[15])
      | ("mode",_,_) -> (p,c@not_mode)
      | _ -> (p,c)
  in List.map aux ops

(*the upper bound of random generation for parameter (s,p1 p2) in general case*)
let upper_bound p1 p2 =
  Int32.to_int (Int32.shift_left Int32.one (p1-p2+1))
;;

(* build the valid value list for parameters *)
(* let valid_lst (ops: ((string * int * int) * int list) list) = *)
(*   let aux ((s', p1, p2), lv) = *)
(*     let value = upper_bound p1 p2 in *)
(*     let length =  *)
(*       if m> 0 && m < Sys.max_array_length *)
(*       then m else Sys.max_array_length in *)
(*     let lst = Array.to_list (Array.init length (fun i -> i)) in *)
(*     let lst' = List.fold_right (fun v -> List.filter ((<>) v)) lv lst in *)
(*       ((s',p1,p2),lst') *)
(*   in List.map aux (other_constr ops) *)
(* ;; *)

let chose_param_value ((_s,p1,p2),cs) =
  let total = upper_bound p1 p2 in
  let keep = total - List.length cs in
  let replacement_list =
    let n = ref keep in
    let generate_replacement () = while List.mem !n cs do n := !n +1 done; !n
    in List.map (fun c -> (c,generate_replacement())) cs
  in
  let candidate = Random.int keep in
    try List.assoc candidate replacement_list with Not_found -> candidate;;

let value_table' ps =
  List.map (fun (p,c) -> (p, chose_param_value (p,c))) (other_constr (mark_params ps));;


let value_table ps =
  let is_s s ((s',_,_),_) = s = s' in
  let v_tb = value_table' ps in 
  let v1 s1 = (fun (_,v) -> v) (List.find (fun l -> is_s s1 l) v_tb)
  and v2 s2 = (fun (_,v) -> v) (List.find (fun l -> is_s s2 l) v_tb) in
  let reg_lst res lst =
    match res with
      | NotSame(s1,s2) -> lst@[((s1,v1),(s2,v2))]
      | OtherVC _|NotV (_, _)|Or (_, _)|NotZero2 (_, _)|NotZero _|IsEven _|NotLR _|
	    NotPC _|BLXbit0|Not2lowRegs|NotLSL0|NoWritebackDest -> lst
  in let notsame_regs = List.fold_right reg_lst (restrict ps) [] in
  let op_ns ((s1,v1),(s2,v2)) lst =
    if v1 == v2 then 
      let cs2 = (fun (_,cs) -> cs) (List.find (fun l -> is_s s1 l)
				      (other_constr (mark_params ps))) in
      List.map (fun ((s,p1,p2),v) -> if is_s s2 ((s,p1,p2),v) then 
		  ((s,p1,p2),chose_param_value ((s,p1,p2),cs2@[v2 s2]))
		else ((s,p1,p2),v)) lst 
    else v_tb
  in match notsame_regs with
    | [] -> v_tb
    | regs -> List.fold_right op_ns regs v_tb
;;   

(*get the vaule from the value table by the name of parameter*)

let get_vs s lst =
  (fun l -> 
     if l = [] then []
     else List.map (fun ((_,_,_),v) -> v)l)
    (List.filter (fun p -> (fun ((s',_,_), _) -> s') p =s) lst)

let get_v s lst =
  match (get_vs s lst) with
    | [] -> raise (Failure (s^" has no value"))
    | ls -> List.nth ls 0
;;

let set_v s nv lst =
  (fun l -> 
     if l = [] then []
     else List.map (fun ((s',p1,p2),v) -> if s' =s
		    then ((s',p1,p2),nv) else ((s',p1,p2),v)) l) lst;;

(*****************************************************************************)
(* binary tests generation*)
(*****************************************************************************)

let gen_tests_bin ps =
  let fix_bits dec =
    match dec with
      | (Shouldbe b, p) -> Insert_bits ((if b then 0b1 else 0b0),p)
      | (Value i, p) -> Insert_bits ((if i then 0b1 else 0b0), p)
      | ((Range _ | Param1 _ | Param1s _ | Nothing), _) -> No_change
  in
  let lst = value_table ps in
  let params (s, _, p2) =
    Insert_bits (get_v s lst, p2)    
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
    Int32.logor 
      (Array.fold_right proc (Array.map fix_bits (pos ps.fdec)) Int32.zero)
      (List.fold_right proc 
	 (List.map params (add_R (parameters_of ps.fdec))) Int32.zero)
;;
    

(*****************************************************************************)
(*assembly tests generation*)
(*****************************************************************************)

(*mask build by the bits from position p1 to p2*)
let mask' p1 p2 =
  let rec aux p n =
    if (n=0) then
      1 lsl p else (1 lsl p) + (aux (p+1) (n-1))
  in aux p2 (p1-p2)
;;

(*get bits value form position p1 to p2*)
let get_bits' p1 p2 w =
  ((mask' p1 p2) land w) lsr p2;;

(*encoding condition*)
let cond v =
  match v with
    | 0 -> "EQ"
    | 1 -> "NE"
    | 2 -> "HS"
    | 3 -> "LO"
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
    | _ -> ""

(*print registers by name*)
let reg r =
  match r with
    | 15 -> "PC"
    | 14 -> "LR"
    | 13 -> "SP"
    (*| 12 -> "IP"
    | 11 -> "FP"
    | 10 -> "LS" *)
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
    | 0b00 -> ""
    | 0b01 -> ", ROR #8"
    | 0b10 -> ", ROR #16"
    | 0b11 -> ", ROR #24"
    | _ -> ""

let mode md =
  match md with
    | 0b10000 -> "usr"
    | 0b10001 -> "fiq"
    | 0b10010 -> "irq"
    | 0b10011 -> "sup"
    | 0b10111 -> "abt"
    | 0b11011 -> "und"
    | 0b11111 -> "sys"
    | _ -> ""

let fields f =
  let c = if (get_bits' 0 0 f) = 1 then "c" else ""
  and x = if (get_bits' 1 1 f) = 1 then "x" else ""
  and s = if (get_bits' 2 2 f) = 1 then "s" else ""
  and f = if (get_bits' 3 3 f) = 1 then "f" else ""
  in c^x^s^f

let coproc cp = "p"^(string_of_int cp)

let sign_ext n x =
  let sign = get_bits n n x in
    if sign = Int32.zero then
       x
    else Int32.logor (get_bits 31 (n+1) Int32.minus_one) x

let target_address si24 =
  Int32.shift_left (sign_ext 24 (Int32.of_int si24)) 2

let target_addr si24 h =
  Int32.add (Int32.shift_left (sign_ext 24 (Int32.of_int si24)) 2) 
    (Int32.shift_left (Int32.of_int h) 1)

let immed_16 is =
  match is with
    | [] -> raise (Failure "no immed")
    | [i] -> Int32.of_int i
    | i1::i2::_ -> Int32.logor (Int32.shift_left (Int32.of_int i1) 4) 
	(Int32.of_int i2)

let m1_immediate r im8 :int32 =
  let rot = r *2 in
  if rot = 0 then
   Int32.of_int im8
  else
    let x = Int32.of_int im8 in
    Int32.logor (Int32.shift_left x (32-rot)) (Int32.shift_right_logical x rot)

let m3_offset_8 h l = Int32.logor (Int32.shift_left (Int32.of_int h) 4) (Int32.of_int l)

let reg_list b regs =
  bprintf b "{";
  let ar = Array.create 16 [] in
    for i = 0 to 15 do
      let regi = (get_bits' i i regs) in
	ar.(i) <- (if regi = 1 then [reg i] else [])
    done;
    (list ", " string) b (List.flatten (Array.to_list ar));
    bprintf b "}"

let reg_list_and_pc b regs =
  bprintf b "{";
  let ar = Array.create 16 [] in
    for i = 0 to 15 do
      let regi = (get_bits' i i regs) in
	ar.(i) <- (if regi = 1 then [reg i] else [])
    done;
    (list ", " string) b (List.flatten (Array.to_list ar));
    bprintf b ", PC}"

let reg_list_without_pc b regs =
  bprintf b "{";
  let ar = Array.create 15 [] in
    for i = 0 to 14 do
      let regi = (get_bits' i i regs) in
	ar.(i) <- (if regi = 1 then [reg i] else [])
    done;
    (list ", " string) b (List.flatten (Array.to_list ar));
    bprintf b "}"

let endian_sp e =
  if e=1 then "BE" else "LE"

let shift si sh =
  if sh = 0 && si >= 0 && si <= 31 then "LSL #"^(string_of_int si)
  else if sh = 1 && si = 0 then "ASR #"^(string_of_int 32)
  else if sh = 1 && si > 0 && si <= 31 then "ASR #"^(string_of_int si)
  else "LSL #0" 

(*main function to generate the instructions in assembly code*)
let asm_insts b ps =
  let aux b tk lst =
    match tk with
      | Const s -> bprintf b "%s" s
      | OptParam (s1, Some s2) -> 
	  begin match s2 with
	    | "cond" as s -> bprintf b "%s%s" s1 (cond (get_v s lst))
	    | "rotation" -> 
		bprintf b "%s" (rotation (get_v "rotate" lst))
	    | "register_list" -> bprintf b "%s" s1; reg_list b (get_v s2 lst)
	    | "shift" ->  
		bprintf b "%s%s" s1 (shift (get_v "shift_imm" lst) 
				       (get_v "shift" lst))
	    | "mode" -> bprintf b "%s%s" s1 (mode (get_v "mode" lst))
	    | _ -> bprintf b "%s%d" s1 (get_v s2 lst)
	  end 
      | OptParam (s, None) ->
	  begin match s with
	    | "L" -> if ps.finstr = "LDC" then bprintf b "L"
	      else if ps.finstr = "STC" then bprintf b ""
	      else if (get_v "L" lst = 1) then bprintf b "%s" s
	      else bprintf b ""
	    | "!" -> if s = "!" && (get_v "W" lst = 1) then 
		bprintf b "!" else bprintf b ""
	    | s -> if (get_v s lst = 1) then bprintf b "%s" s
	      else bprintf b ""		
	  end 
      | Param s -> 
	  begin match s with
	    | ("Rd"|"Rn"|"Rs"|"Rm"|"RdHi"|"RdLo") as s -> 
		bprintf b "%s" (reg (get_v s lst))
	    | ("CRn"|"CRm"|"CRd") as s ->
		bprintf b "CR%d" (get_v s lst)
	    | ("x"|"y") as s -> bprintf b "%s" (xy (get_v s lst))
	    | "iflags" -> 
		bprintf b "%s" (iflags (get_v "A" lst) (get_v "I" lst) 
				  (get_v "F" lst))
	    | "effect" -> bprintf b "%s" (effect (get_v "imod" lst))
	    | "coproc" -> bprintf b "%s" (coproc (get_v "cp_num" lst))
	    | "registers" -> 
		reg_list b (get_v "register_list" lst)
	    | "registers_and_pc" ->
		reg_list_and_pc b (get_v "register_list" lst)
	    | "registers_without_pc" ->
		reg_list_without_pc b (get_v "register_list" lst)
	    | "immediate" as s->
		begin match ps.finstr with
		  | "MSRimm" -> 
		      bprintf b "0x%lx" (m1_immediate 
					      (get_v "rotate_imm" lst) 
					      (get_v "immed_8" lst))
		  | _ -> 
		      begin match ps.fmode with
			| Some "M1_Imm" ->
			    bprintf b "0x%lx" (m1_immediate 
					      (get_v "rotate_imm" lst) 
					      (get_v "immed_8" lst))
			| _ -> bprintf b "%d" (get_v s lst)
		      end
		end
	    | "fields" -> bprintf b "%s" (fields (get_v "field_mask" lst))
	    | "target_address" -> 
		bprintf b "PC+#0x%lx" (target_address (get_v "signed_immed_24" lst))
	    |"target_addr" -> bprintf b "PC+#0x%lx" 
	       (target_addr (get_v "signed_immed_24" (set_v "H" 1 lst)) 
	       (get_v "H" (set_v "H" 1 lst)))
	    | "immed" as s-> 
		begin match ps.finstr with
		  | "SSAT"| "SSAT16"| "USAT"| "USAT16" -> 
		      bprintf b "%d" ((get_v "sat_imm" lst))
		  | _ -> bprintf b "%d" (get_v s lst)
		end
	    | "immed_16" -> 
		bprintf b "0x%lx" (immed_16 (get_vs "immed" lst))
	    | "immed_24" as s -> bprintf b "0x%x" (get_v s lst)
	    | "offset_8" as s ->
		begin match ps.fmode with
		  | Some "M3_ImmOff" | Some "M3_Imm_postInd" | Some "M3_Imm_preInd" ->
		      bprintf b "0x%lx" (m3_offset_8 
					(get_v "immedH" lst) 
					(get_v "immedL" lst))
		  | _ -> bprintf b "%d" (get_v s lst)
		end
	    | "endian_specifier" ->
		bprintf b "%s" (endian_sp (get_v "E" lst))
	    | "shift_imm" as s ->
		bprintf b "%d" (if get_v s lst = 32 then 0 else get_v s lst)
	    | "offset_12" as s -> bprintf b "0x%x" (get_v s lst)
	    | "mode" as s -> bprintf b "%s" (mode (get_v s lst))
	    | _ -> bprintf b "%d" (get_v s lst)
	  end
      | PlusMinus -> if (get_v "U" lst = 1) then bprintf b "+"
	else bprintf b "-"
  in let rec aux2 b var lst =
      match var with
	| [] -> bprintf b ""
	| tk::tks -> aux b tk lst; aux2 b tks lst
  in let rec aux3 b syn lst =
      match syn with
	| [] -> raise (Failure "empty syntax list")
	| [v] ->  aux2 b v lst; bprintf b "\n";
	| [c; nc] when List.mem (Param "coproc") c ->
	    if (get_v "cond" lst) = 0xf then  aux2 b nc lst
	    else aux2 b c lst; bprintf b "\n"
        | [e; ne] when ps.fid = "CPS" ->
	    if (get_v "imod" lst) = 1 then aux2 b ne lst
	    else aux2 b e lst; bprintf b "\n"
        | [ll; lr; ar; rr; rx] ->
	    (match (get_v "shift" lst) with
	      | 0 -> aux2 b ll lst; bprintf b "\n"
	      | 1 -> aux2 b lr lst; bprintf b "\n"
	      | 2 -> aux2 b ar lst; bprintf b "\n"
	      | 3 -> 
		  if (get_v "shift_imm" lst) = 0 then
		    aux2 b rx lst
		  else aux2 b rr lst; bprintf b "\n"
	      | _ -> raise (Failure "not a shift operand"))	
        | [cpsr; spsr] when List.mem ps.fid ["MRS"; "MSRimm"; "MSRreg"] ->
	    if (get_v "R" lst) = 1 then
	      aux2 b spsr lst
	    else aux2 b cpsr lst; 
	    bprintf b "\n"          
        | _ -> raise (Failure ("case not implemented: "^ps.fid))
  in aux3 b ps.fsyntax (value_table ps)
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
  let cp_instr = ["LDC";"STC";"MRRC";"MRC";"MCR";"MCRR";"CDP" ] in
  let fs' = List.filter (fun f -> not (List.mem f.finstr cp_instr)) fs in
    List.iter (bin_insts out) (List.rev fs')
;;

(*****************************************************************************)
(*output assembly tests*)
(*****************************************************************************)

let gen_asm_test bn pcs ss decs seed =
  Random.init seed;
  let fs: fprog list = List.filter is_arm (flatten pcs ss decs) in
  let cp_instr = ["LDC";"STC";"MRRC";"MRC";"MCR";"MCRR";"CDP" ] in
  let fs' = List.filter (fun f -> not (List.mem f.finstr cp_instr)) fs in
  let ba = Buffer.create 100000 in
    (list "" asm_insts) ba (List.rev fs');
    let outa = open_out (bn^".asm") in
      Buffer.output_buffer outa ba; close_out outa;
;;

let gen_test bn pcs ss decs seed =
  Random.init seed;
  let fs: fprog list = List.filter is_arm (flatten pcs ss decs) in
  let cp_instr = ["LDC";"STC";"MRRC";"MRC";"MCR";"MCRR";"CDP" ] in
  let fs' = List.filter (fun f -> not (List.mem f.finstr cp_instr)) fs in
  let ba = Buffer.create 100000 in
  let bb = Buffer.create 100000 in
    (list "" asm_insts) ba (List.rev fs');
    let outa = open_out (bn^".asm") and outb = open_out (bn^".bin") in
      set_binary_mode_out outb true;
      List.iter (bin_insts outb) (List.rev fs');
      Buffer.output_buffer outa ba; close_out outa;
      Buffer.output_buffer outb bb; close_out outb
;;
