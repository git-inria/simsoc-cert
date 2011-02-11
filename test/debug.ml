#directory "../extract/tmp";;
#load "extract.cma";;

open Arm
open BinInt
open BinPos
open Bitvec
open Datatypes
open Integers
open Arm_Proc
open Arm_SCC
open Simul
open Arm_State
open Util
open Arm6
open Semantics
open Arm_Functions

let str_of_msg = function
  | Message.EmptyMessage -> "EmptyMessage"
  | Message.ImpreciseDataAbort -> "ImpreciseDataAbort"
  | Message.InvalidInstructionSet -> "InvalidInstructionSet"
  | Message.JazelleInstructionSetNotImplemented -> "JazelleInstructionSetNotImplemented"
  | Message.ThumbInstructionSetNotImplemented -> "ThumbInstructionSetNotImplemented"
  | Message.DecodingReturnsUnpredictable -> "DecodingReturnsUnpredictable"
  | Message.StartOpcodeExecutionAt -> "StartOpcodeExecutionAt"
  | Message.While -> "While"
  | Message.Coproc -> "Coproc"
  | Message.Affect -> "Affect"
  | Message.Case -> "Case"
  | Message.ComplexSemantics -> "ComplexSemantics"
  | Message.NotAnAddressingMode1 -> "NotAnAddressingMode1"
  | Message.NotAnAddressingMode2 -> "NotAnAddressingMode2"
  | Message.NotAnAddressingMode3 -> "NotAnAddressingMode3"
  | Message.NotAnAddressingMode4 -> "NotAnAddressingMode4"
  | Message.NotAnAddressingMode5 -> "NotAnAddressingMode5";;

let nat =
 let rec aux = function
   | 0 -> O
   | k -> S (aux (k-1))
 in fun k ->
   if k < 0 then invalid_arg "not a nat"
   else aux k;;

let rec nat_to_int = function
  | O -> 0
  | S n -> 1 + nat_to_int n;; 

let rec positive = function
 | x when x <= 0 -> invalid_arg "not a positive"
 | 1 -> Coq_xH
 | x when x mod 2 = 0 -> Coq_xO (positive (x/2))
 | x -> Coq_xI (positive (x/2));;

let coq_Z = function
 | 0 -> Z0
 | x when x < 0 -> Zneg (positive (-x))
 | x -> Zpos (positive x);;

let simul lbs = 
  let n = nat_to_int (nb_next lbs) in
  Simul.catch S.simul (fun m lbs ->
    let num = nb_next lbs in
    let step = string_of_int (n - nat_to_int num) in
    failwith ("SimKo: " ^ str_of_msg m ^ " at step " ^ step)) lbs;;

let next = 
  Simul.bind (fun lbs -> SimOk ((), { lbs with nb_next = n1 }))
    (fun () -> simul);;

let rec positive_to_int = function
  | Coq_xH -> 1
  | Coq_xO p -> 2*(positive_to_int p)
  | Coq_xI p -> 2*(positive_to_int p)+1;;

let coq_Z_to_int = function
  | Z0 -> 0
  | Zneg p -> -(positive_to_int p)
  | Zpos p -> positive_to_int p;;

let regz s n = Arm_Proc.reg (Arm_State.proc s) (R (coq_Z n));;
let reg s n = coq_Z_to_int (regz s n);;

let read_z s a = read s (coq_Z a) Bitvec.Word;;

let read_word s a = coq_Z_to_int (read_z s a);;

let rec read_words s a n =
  if n = 0 then []
  else read_word s a :: read_words s (a+4) (n-1);;

(* current instruction *)
let instr s =
  Arm6dec.decode (read s (address_of_current_instruction s) Word);;

(* display the stack *)
let stack s =
  let stack_top = 0xff000 in (* value given in common.h*)
  let sp = reg s 13 in
    if (sp>stack_top) then raise (Failure "stack pointer above stack")
    else read_words s sp ((stack_top-sp)/4);;

let return a lbs = SimOk (a, lbs)

let mk_st state steps = 
  { semst = { loc = [] ; bo = true ; s0 = state ; st = state } ; nb_next = nat steps }

let check state steps expected name =
  try
    ignore (Simul.bind simul (fun () -> Simul.get_st (fun s -> 
      return (if reg s 0 = expected then print_endline (name^" OK.")
        else (
          print_string ("Error in "^name^", r0 = ");
          Printf.printf "%d (0x%x)" (reg s 0) (reg s 0); print_string " instead of ";
          Printf.printf "%d (0x%x)" expected expected; print_endline "."
        ))
    )) (mk_st state steps))
  with Failure s -> print_endline ("Error in "^name^": "^s^".");;


let pc s = Printf.printf "address of current instruction = 0x%x\n" ((reg s 15) - 8);;

let print_coq_Z f n = Format.fprintf f "%d (0x%x)" (coq_Z_to_int n) (coq_Z_to_int n);;
#install_printer print_coq_Z;;

type hexa = Ox of int;;
let print_hexa f = function Ox n -> Format.fprintf f "0x%x" n;;
#install_printer print_hexa;;

let run_opt (max : int option) : (BinInt.coq_Z * (int * hexa) list) Simul.simul_semfun =
  let rec aux : (int * hexa) list -> (int * hexa) list Simul.simul_semfun = function
    | (step, Ox pc) :: l' as l ->
      if Some step = max then return l
      else
        Simul.bind Simul.save_s0_true (fun () -> 
        Simul.bind next (fun () -> 
        get_st (fun s' -> 
        let pc' = (reg s' 15) - 8 in
        (if pc' = pc then return
         else if pc' = pc+4 then aux
         else function x :: xs -> aux (x :: x :: xs) | _ -> assert false)
          ((step+1, Ox pc') :: l')
       )))
    | _ -> raise (Failure "inside run function")
  in 

  Simul.bind (get_s0 (fun s0 -> aux [ (0, Ox ((reg s0 15) - 8))
                                    ; (0, Ox ((reg s0 15) - 8))]))
    (fun l -> 
      get_st (fun sn -> return (regz sn 0, l)));;

let run s0 = run_opt None (mk_st s0 1);;
let runmax s0 max = run_opt (Some max) (mk_st s0 1);;

#load "arm_v6_QADD_a.cmo";;
check Arm_v6_QADD_a.initial_state 509 0x7efff "arm_v6_QADD";;

#load "arm_v6_REV_a.cmo";;
check Arm_v6_REV_a.initial_state 125 15 "arm_v6_REV";;

#load "arm_v6_SADD_a.cmo";;
check Arm_v6_SADD_a.initial_state 742 0x1FFFFFF "arm_v6_SADD";;

#load "arm_v6_SSUB_a.cmo";;
check Arm_v6_SSUB_a.initial_state 638 0xfffff "arm_v6_SSUB";;

#load "arm_v6_SSAT_a.cmo";;
check Arm_v6_SSAT_a.initial_state 632 0xfff "arm_v6_SSAT";;

#load "arm_v6_SSUB_a.cmo";;
check Arm_v6_SSUB_a.initial_state 638 0xfffff "arm_v6_SSUB";;

#load "arm_v6_SXTA_a.cmo";;
check Arm_v6_SXTA_a.initial_state 414 0x7fff "arm_v6_SXTA";;

#load "arm_v6_SXTB_a.cmo";;
check Arm_v6_SXTB_a.initial_state 411 0x7fff "arm_v6_SXTB";;

#load "arm_v6_UMAAL_a.cmo";;
check Arm_v6_UMAAL_a.initial_state 207 0xff "arm_v6_UMAAL";;

#load "arm_v6_UH_a.cmo";;
check Arm_v6_UH_a.initial_state 594 0x3ffff "arm_v6_UH";;

#load "arm_v6_SH_a.cmo";;
check Arm_v6_SH_a.initial_state 205 63 "arm_v6_SH";;

#load "arm_v6_SM_a.cmo";;
check Arm_v6_SM_a.initial_state 617 0x3ffff "arm_v6_SM";;

#load "arm_multiple_a.cmo";;
check Arm_multiple_a.initial_state 227 0x1ff "arm_multiple";;

#load "arm_edsp_a.cmo";;
check Arm_edsp_a.initial_state 679 8388607 "arm_edsp";;

#load "sum_iterative_a.cmo";;
check Sum_iterative_a.initial_state 264 903 "sum_iterative";;

#load "sum_recursive_a.cmo";;
check Sum_recursive_a.initial_state 740 903 "sum_recursive";;

#load "sum_direct_a.cmo";;
check Sum_direct_a.initial_state 18 903 "sum_direct";;

#load "arm_blx2_a.cmo";;
check Arm_blx2_a.initial_state 26 3 "arm_blx2";;

#load "arm_cflag_a.cmo";;
check Arm_cflag_a.initial_state 100 15 "arm_cflag";;

#load "arm_dpi_a.cmo";;
check Arm_dpi_a.initial_state 964 524287 "arm_dpi";;

#load "arm_ldmstm_a.cmo";;
check Arm_ldmstm_a.initial_state 119 7 "arm_ldmstm";;

#load "arm_ldrd_strd_a.cmo";;
check Arm_ldrd_strd_a.initial_state 181 255 "arm_ldrd_strd";;

#load "arm_ldrstr_a.cmo";;
check Arm_ldrstr_a.initial_state 486 0x7ffffff "arm_ldrstr";;

#load "arm_mrs_a.cmo";;
check Arm_mrs_a.initial_state 727 0x7ffff "arm_mrs";;

#load "arm_msr_a.cmo";;
check Arm_msr_a.initial_state 639 0x1ffff "arm_msr";;

#load "arm_swi_a.cmo";;
check Arm_swi_a.initial_state 45 3 "arm_swi";;

#load "endian_a.cmo";;
check Endian_a.initial_state 96 7 "endian";;

#load "multiply_a.cmo";;
check Multiply_a.initial_state 130 15 "multiply";;

#load "test_mem_a.cmo";;
check Test_mem_a.initial_state 313 3 "test_mem";;

(* #load "simsoc_new1_a.cmo";; *)
(* check Simsoc_new1_a.initial_state 190505 255 "simsoc_new1";; *)

(* #load "sorting_a.cmo";; *)
(* check Sorting_a.initial_state 2487176 63 "sorting";; *)
