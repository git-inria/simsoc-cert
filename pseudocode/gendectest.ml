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

let push_pc (x: int32) = 
  push_bit false (push_bit true (push_bit true (push_bit true x)));;  

let insert_bit (b: int32) (p: int) (w: int32) =
  let i = Int32.shift_left b p in
    Int32.logor i w;;

let insert_bits i p w =
  let is = Int32.shift_left i p in
    Int32.logor is w;;

type vcon =
  | Insert_bits of int *int
  | Insert_bit of bool * int
  | No_change
;;
(*
let gen_pre pc =
  let aux ls w =
    match ls with
      | Value s -> push_bit s w
      | Shouldbe s -> push_bit s w
      | Range ("cond", _, _) -> push_bit (Random.bool ()) w
      | Param1 _ | Param1s _ -> push_bit false w
      | Range _ -> push_bit false w
      | Nothing -> raise (Failure "unexpected case")
  in Array.fold_right aux pc.fdec Int32.zero;;

let gen_bin pc =
  let aux ls w =
    match ls with
      | Value s -> push_bit s w
      | Shouldbe s -> push_bit s w
      | Param1 _ | Param1s _ -> push_bit (Random.bool ()) w
      | Range _ -> push_bit (Random.bool ()) w
      | Nothing -> raise (Failure "unexpected case")
  in Array.fold_right aux pc Int32.zero;;
*)

let gen_tests ps =
  let aux1 dec =
    match dec with
      | (Shouldbe b, p) -> Insert_bit (b,p)
      | (Value i, p) -> Insert_bit (i, p)
      | ((Range _ | Param1 _ | Param1s _ | Nothing), _) -> No_change
  in
  let max_v i1 i2 =
    if i2 >= i1 then
      int_of_float (2.0** (float (i2-i1+1)))
    else 1
  in
  let aux2 para =
    match para with
      | (("n"|"m"|"s"|"d"|"dLo"|"dHi"),_, p2) -> Insert_bits (Random.int 15, p2)
      | (("cond"),_, p2) -> Insert_bits (Random.int 15, p2)
      | (_, p1, p2) -> 
	  Insert_bits (Random.int (max_v p1 p2), p2)
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
  in match ps.finstr with
    | "ADC"  -> 
	Int32.logor (Array.fold_right proc (Array.map aux1 (pos ps.fdec)) Int32.zero)
	  (List.fold_right proc (List.map aux2 (parameters_of ps.fdec)) Int32.zero)
    | _ -> Int32.zero
;;


(*let gen_unpred (lh, ls) =
  let aux lh ls =
    match name (lh, ls) with
      | ("BLX2"|"BXJ") :: _ -> NotPC ("m", 0)
      | "CLZ" :: _ -> Or (NotPC ("m", 0), NotPC ("d", 12))
      | "CPS"::_ -> Or (And (NotV ("mmod",Int32.zero,18), NotVs ("immod", 0b00,16)), 
			Or (And (NotV ("mmod",Int32.zero,18), NotVs ("immod", 0b01,16)), 
			    And (NotV ("mmod",Int32.one,18), NotVs ("immod", 0b01,16))))
      | ("LDM1"|"LDM2"|"STM1"|"STM2") ::_ -> And (NotPC ("n", 16), NotZero 0)
      | "LDM3" :: _ -> NotPC ("n", 16)
      | ("LDR"|"STR"|"STRB") :: _ -> NoWritebackDest
      | "LDRB" :: _ -> NotPC ("n", 16)
      | "LDRBT" :: _ -> Or (NotPC ("n", 16), NotSame (16, 12))
      (*| "LDRD" :: _ -> *)
      | "LDREX" :: _ -> Or (NotPC ("n", 16), NotPC ("d", 12))
      | ("LDRH"|"LDRSB"|"LDRSH"|"STRH") :: _ -> Or (NotPC ("d", 12), NoWritebackDest)
      | ("LDRT"|"STRBT") :: _ -> Or (NotPC ("d", 12), NotSame (16, 12))
      | "MCR" :: _ -> NotPC ("d", 12)
      | "MCRR" :: _ -> NotPC ("d" , 12)
      | ("MLA"|"SMLAxy"|"SMLAWy"|"SMLSD"|"SMMLS") :: _  -> 
	  Or (NotPC ("d", 16), Or (NotPC ("m", 0), Or (NotPC ("s", 8), NotPC ("n", 12))))
      | "MRRC" :: _ -> Or (NotSame (12, 16), Or (NotPC ("d", 12), NotPC ("n", 16)))
      | "MRS" :: _ -> NotPC ("d", 12)
      | "MUL" :: _ -> Or (NotPC ("d", 16), Or (NotPC ("s", 8), NotPC ("m",0)))
      | ("PKHBT"|"PKHTB"|"QADD"|"QADD8"|"QADD16"|"QADDSUBX"|"QDADD"|"QDSUB"|"QSUB"|"QSUB16"|"QSUB8"|"QSUBADDX"|"SADD16"|"SADD8"|"SADDSUBX"|"SEL"|"SHADD16"|"SHADD8"|"SHADDSUBX"|"SHSUB16"|"SHSUB8"|"SHSUBADDX"|"SSUB16"|"SSUB8"|"SSUBADDX") :: _ 
	-> Or (NotPC ("n", 16), Or (NotPC ("d", 12), NotPC ("m", 0)))
      | ("REV"|"REV16"|"REVSH"|"SSAT"|"SSAT16"|"SXTAB"|"SXTAB16"|"SXTAH"|"SXTB"|"SXTB16"|"SXTH") :: _ -> Or (NotPC ("d", 12), NotPC ("m", 0))
      | "RFE" :: _ -> NotPC ("n", 16)
      | "SMLAD" :: _ -> Or (NotPC ("d",16), Or (NotPC ("m",0), NotPC ("s",8)))
      | "SMLAL" :: _ -> Or (NotPC ("dHi", 16), Or (NotPC ("dLo", 12), Or (NotPC ("s", 8), NotPC ("m",0))))
      | ("SMLALxy"|"SMLALD"|"SMLSLD"|"SMULL"|"UMAAD"|"UMLAL"|"UMULL") :: _ -> Or (NotPC ("dHi", 16), Or (NotPC ("dLo", 12), Or (NotPC ("s", 8), Or (NotPC ("m",0), NotSame (16,12)))))
      | ("SMMUL"|"SMUAD"|"SMULxy"|"SMULWy"|"SMUSD"|"USAD8"|"USADA8"):: _ -> Or (NotPC ("d", 16), Or (NotPC ("s", 8), NotPC ("m", 0)))
      (*| STRD ->*)
      | "STREX" :: _ -> Or (NotPC ("n",16), Or (NotPC ("d",12), Or (NotPC ("m",0), Or (NotSame (12,0), NotSame (12,16)))))
      | "STRT" :: _ -> NotSame (16,12)
      | ("SWP"|"SWPB") :: _ -> Or (NotPC ("n",16), Or (NotPC ("d",12), Or (NotPC ("m",0), Or (NotSame (16,0), NotSame (16,12)))))
      | ("UADD16"|"UADD8"|"UADDSUBX"|"UHADD16"|"UHADD8"|"UHADDSUBX"|"UHSUB16"|"UHSUB8"|"UHSUBADDX"|"UQADD16"|"UQADD8"|"UQADDSUBX"|"UQSUB16"|"UQSUB8"|"UQSUBADDX"|"USUB16"|"USUB8"|"USUBADDX") :: _ -> Or (NotPC ("n",16), Or (NotPC ("d",12), NotPC ("m",0)))
      | ("USAT"|"USAT16"|"UXTAB"|"UXTAB16"|"UXTAH"|"UXTB"|"UXTB16"|"UXT H") :: _ -> Or (NotPC ("d", 12), NotPC ("m",0))
      | _ -> General
  in
  let rec aux2 m w =
    match m with
      | NotPC (_, p) -> insert_bits (Int32.of_int 15) p w
      | NotLR (_, p) -> insert_bits (Int32.of_int 14) p w
      | NotZero i -> insert_bit (Int32.of_int 0b000000000000000) i w
      
      | NotV (_,i,p) -> insert_bit i p w
      | NotVs (_,s,p) ->  insert_bits (Int32.of_int s) p w
      (*| And (NotV (_, i1,p1), NotV (_,i2,p2)) -> insert_bit i1 p1 (insert_bits i2 p2 w)*)
      | NotSame (i1, i2) -> let r = (Random.int32 (Int32.of_int 0b1111)) in
	  insert_bits r i1 (insert_bits r i2 w)
      | NoWritebackDest -> insert_bit Int32.one 21 w
      | Or (v1, v2) -> if Random.bool () then (aux2 v1 w) else (aux2 v2 w)
      | And (v1, v2) -> aux2 v1 (aux2 v2 w)
      | General 
	  -> gen_bin ls
  in aux2 (aux lh ls) (gen_pre ls)
;;

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

let bin_insts out fs =
    output_word out (gen_tests fs)
;;

let gen_test out pcs decs =
  set_binary_mode_out out true;
  let fs: fprog list = List.filter is_arm (flatten pcs decs) in
    List.iter (bin_insts out) fs;;
