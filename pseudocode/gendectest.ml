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

(*let gen_unpre x =
  let aux ls w =
  match ls with
    | Range (("m","n","s","d"),_,_) -> Int32.of_string "0o15"
    | Shouldbe true -> push_bit Int32.zero w
    | Shouldbe false -> push_bit Int32.one w
    | Range _ -> push_bit (Random.bool ())
    | Value _| Shouldbe _| Param1 _| Param1s _| Range _| Nothing
;;
*)

let push_bits x y =
  let lst = Array.to_list x in
    List.fold_right push_bit lst y;; 

let push_pc x = 
  push_bit false (push_bit true (push_bit true (push_bit true x)));;  

type vconstraint =
  | NotPC of string * int   (* the string must contains the name of parameter *)
  | NotLR of string * int (* the string must contains the name of parameter *)
  | IsEven of string   (* parameter that should contain an even value *)
  (*| NotZero of int  (* parameter that should not be zero *)
  | NotOne of int*)
  | NoWritebackDest    (* no write-back with Rd==Rn *)
  | NotSame of int * int (* R<a> <> R<b> *)
  | NotLSL0            (* to distinguished between (equivalent?) mode cases *)
  | OtherVC of exp     (* Other validy constraints described by a boolean
                        * expression *)
  | NotV of string * int32 * int
  | NotVs of string * int * int
  | And of vconstraint * vconstraint
  | NotZero of int
  | Or of vconstraint * vconstraint
  | General
;;

let insert_bit b p w =
  let i = Int32.shift_left b p in
    Int32.logor i w;;

let insert_bits i p w =
  let is = Int32.shift_left i p in
    Int32.logor is w;;

let gen_unpred (lh, ls) =
  let aux lh ls =
    match name (lh, ls) with
      | ("BLX2"|"BXJ") :: _ -> NotPC ("m", 0)
      | "CLZ" :: _ -> And (NotPC ("m", 0), NotPC ("d", 12))
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
      | ("USAT"|"USAT16"|"UXTAB"|"UXTAB16"|"UXTAH"|"UXTB"|"UXTB16"|"UXTH") :: _ -> Or (NotPC ("d", 12), NotPC ("m",0))
      | _ -> General
  in
  let aux2 m w =
    match m with
      | NotPC (_, i) -> insert_bits (Int32.of_int 0b1111) i w
      | NotLR (_, i) -> insert_bits (Int32.of_int 0b1110) i w
      (*| NotOne i -> insert_bit Int32.one i w*)
      | NotZero i -> insert_bit (Int32.of_int 0b000000000000000) i w
      
      | NotV (_,i,p) -> insert_bit i p w
      | NotVs (_,s,p) ->  insert_bits (Int32.of_int s) p w
      | And (NotV (_, i1,p1), NotV (_,i2,p2)) -> insert_bit i1 p1 (insert_bits i2 p2 w)
      | NotSame (i1, i2) -> let r = (Random.int32 (Int32.of_int 0b1111)) in
	  insert_bits r i1 (insert_bits r i2 w)
      | NoWritebackDest -> insert_bit Int32.one 21 w
      | General | And _ | IsEven _| OtherVC _
      | NotLSL0|Or _
	  -> push_bit (Random.bool ()) w
  in aux2 (aux lh ls) Int32.zero
;;

let gen_bin pc =
  let aux ls w =
    match ls with
      | Value s -> push_bit s w
      | Shouldbe s -> push_bit s w
      | Param1 _ | Param1s _ -> push_bit (Random.bool ()) w
      | Range _ -> push_bit (Random.bool ()) w
      | Nothing -> raise (Failure "unexpected case")
  in Array.fold_right aux pc Int32.zero;;

let bin_inst out (lh, ls) =
  let md = add_mode (name (lh,ls)) in
    match md with
      | DecInst -> (*output_word out (gen_bin ls)*)
	  output_word out (gen_unpred (lh, ls))
      | DecEncoding -> ()
      | DecMode _ -> ();;

let gen_test out ps =
  set_binary_mode_out out true;
  List.iter (bin_inst out) ps;;
