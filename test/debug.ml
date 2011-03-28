(*
SimSoC-Cert, a toolkit for generating certified processor simulators
See the COPYRIGHTS and LICENSE files
*)

open BinInt
open BinPos
open Bitvec
open Datatypes

let str_of_msg = 
  let open Message in
  function
  | EmptyMessage -> "EmptyMessage"
  | ImpreciseDataAbort -> "ImpreciseDataAbort"
  | InvalidInstructionSet -> "InvalidInstructionSet"
  | JazelleInstructionSetNotImplemented -> "JazelleInstructionSetNotImplemented"
  | ThumbInstructionSetNotImplemented -> "ThumbInstructionSetNotImplemented"
  | DecodingReturnsUnpredictable -> "DecodingReturnsUnpredictable"
  | StartOpcodeExecutionAt -> "StartOpcodeExecutionAt"
  | While -> "While"
  | Coproc -> "Coproc"
  | Affect -> "Affect"
  | Case -> "Case"
  | ComplexSemantics -> "ComplexSemantics"
  | NotAnAddressingMode1 -> "NotAnAddressingMode1"
  | NotAnAddressingMode2 -> "NotAnAddressingMode2"
  | NotAnAddressingMode3 -> "NotAnAddressingMode3"
  | NotAnAddressingMode4 -> "NotAnAddressingMode4"
  | NotAnAddressingMode5 -> "NotAnAddressingMode5";;

module type TEST = 
sig
  type state 
  val check : state -> int32 -> int32 -> string -> unit
end

module Arm_Test : TEST with type state = Arm_State.state =
struct
  type state = Arm_State.state

let simul lbs = 
  let n = Camlcoq.camlint_of_nat (Arm6.Simul.nb_next lbs) in
  Arm6.Simul.catch Arm6.S.simul (fun m lbs ->
    let num = Arm6.Simul.nb_next lbs in
    let step = string_of_int (n - Camlcoq.camlint_of_nat num) in
    failwith ("SimKo: " ^ str_of_msg m ^ " at step " ^ step)) lbs;;

let next = 
  Arm6.Simul.bind (fun lbs -> Arm6.Simul.SimOk ((), { lbs with Arm6.Simul.nb_next = n1 }))
    (fun () -> simul);;

let (+) = Int32.add
let (-) = Int32.sub
let (/) = Int32.div

let regz s n = Arm_Proc.reg (Arm_State.proc s) (Arm.R (Camlcoq.z_of_camlint n));;
let reg s n = Camlcoq.camlint_of_coqint (regz s n);;

let read_z s a = Arm_State.read s (Camlcoq.z_of_camlint a) Bitvec.Word;;
let read_word s a = Camlcoq.camlint_of_z (read_z s a);;

let rec read_words s a n =
  if n = 0_l then []
  else read_word s a :: read_words s (a+4_l) (n-1_l);;

(* current instruction *)
let instr s =
  Arm6dec.decode (Arm_State.read s (Arm_State.address_of_current_instruction s) Word);;

(* display the stack *)
let stack s =
  let stack_top = 0xff000_l in (* value given in common.h*)
  let sp = reg s 13_l in
    if (sp>stack_top) then Pervasives.raise (Failure "stack pointer above stack")
    else read_words s sp ((stack_top-sp)/4_l);;

let return a lbs = Arm6.Simul.SimOk (a, lbs)

let mk_st state steps = 
  { Arm6.Simul.semst = { Arm_Functions.Semantics.S.loc = [] ; bo = true ; st = state } ; nb_next = Camlcoq.nat_of_camlint steps }

let get_st f x = f x.Arm6.Simul.semst.Arm_Functions.Semantics.S.st x

let check state steps expected name =
  try
    ignore (Arm6.Simul.bind simul (fun () -> get_st (fun s -> 
      return (if reg s 0_l = expected then print_endline (name^" OK.")
        else (
          print_string ("Error in "^name^", r0 = ");
          Printf.printf "%ld (0x%lx)" (reg s 0_l) (reg s 0_l); print_string " instead of ";
          Printf.printf "%ld (0x%lx)" expected expected; print_endline "."
        ))
    )) (mk_st state steps))
  with Failure s -> print_endline ("Error in "^name^": "^s^".");;


let pc s = Printf.printf "address of current instruction = 0x%lx\n" ((reg s 15_l) - 8_l);;

let print_coq_Z f n = Format.fprintf f "%ld (0x%lx)" (Camlcoq.camlint_of_z n) (Camlcoq.camlint_of_z n);;
(*#install_printer print_coq_Z;;*)

type hexa = Ox of int32;;
let print_hexa f = function Ox n -> Format.fprintf f "0x%lx" n;;
(*#install_printer print_hexa;;*)

let run_opt (max : int32 option) : (BinInt.coq_Z * (int32 * hexa) list) Arm6.Simul.simul_semfun =
  let rec aux : (int32 * hexa) list -> (int32 * hexa) list Arm6.Simul.simul_semfun = function
    | (step, Ox pc) :: l' as l ->
      if Some step = max then return l
      else
        Arm6.Simul.bind Arm6.Simul.conjure_up_true (fun () -> 
        Arm6.Simul.bind next (fun () -> 
        get_st (fun s' -> 
        let pc' = (reg s' 15_l) - 8_l in
        (if pc' = pc then return
         else if pc' = pc+4_l then aux
         else function x :: xs -> aux (x :: x :: xs) | _ -> assert false)
          ((step+1_l, Ox pc') :: l')
       )))
    | _ -> Pervasives.raise (Failure "inside run function")
  in 

  Arm6.Simul.bind (get_st (fun s0 -> aux [ (0_l, Ox ((reg s0 15_l) - 8_l))
                                           ; (0_l, Ox ((reg s0 15_l) - 8_l))]))
    (fun l -> 
      get_st (fun sn -> return (regz sn 0_l, l)));;

let run s0 = run_opt None (mk_st s0 1_l);;
let runmax s0 max = run_opt (Some max) (mk_st s0 1_l);;

end


let _ = 
  let check f n1 n2 = Arm_Test.check f (Int32.of_int n1) (Int32.of_int n2) in
  begin
    check Arm_v6_QADD_a.initial_state 516 0x7ffff "arm_v6_QADD";
    check Arm_v6_QSUB_a.initial_state 790 0x3fffffff "arm_v6_QSUB";
    check Arm_v6_UQADD_a.initial_state 487 0x7FFFF "arm_v6_UQADD";
    check Arm_v6_UQSUB_a.initial_state 760 0x3FFFFFFF "arm_v6_UQSUB";
    check Arm_v6_USAT_a.initial_state 362 0xfff "arm_v6_USAT";
    check Arm_v6_SHSUB_a.initial_state 205 63 "arm_v6_SHSUB";
    check Arm_v6_USAD_a.initial_state 259 255 "arm_v6_USAD";
    check Arm_v6_UA_a.initial_state 749 0x1FFFFFF "arm_v6_UA";
    check Arm_v6_USUB_a.initial_state 638 0xfffff "arm_v6_USUB";
    check Arm_v6_SML_a.initial_state 313 255 "arm_v6_SML";
    check Arm_v6_SMM_a.initial_state 193 63 "arm_v6_SMM";
    check Arm_v6_SMU_a.initial_state 991 0xFFFFFFF "arm_v6_SMU";
    check Arm_v6_UXTA_a.initial_state 414 0x7FFF "arm_v6_UXTA";
    check Arm_v6_UXTB_a.initial_state 411 0x7fff "arm_v6_UXTB";
    check Arm_v6_SHADD_a.initial_state 205 63 "arm_v6_SHADD";
    check Arm_v6_REV_a.initial_state 125 15 "arm_v6_REV";
    check Arm_v6_SADD_a.initial_state 742 0x1FFFFFF "arm_v6_SADD";
    check Arm_v6_SSUB_a.initial_state 638 0xfffff "arm_v6_SSUB";
    check Arm_v6_SSAT_a.initial_state 632 0xfff "arm_v6_SSAT";
    check Arm_v6_SSUB_a.initial_state 638 0xfffff "arm_v6_SSUB";
    check Arm_v6_SXTA_a.initial_state 414 0x7fff "arm_v6_SXTA";
    check Arm_v6_SXTB_a.initial_state 411 0x7fff "arm_v6_SXTB";
    check Arm_v6_UMAAL_a.initial_state 207 0xff "arm_v6_UMAAL";
    check Arm_v6_UH_a.initial_state 594 0x3ffff "arm_v6_UH";
    check Arm_v6_SHADD_a.initial_state 205 63 "arm_v6_SHADD";
    check Arm_v6_SHSUB_a.initial_state 205 63 "arm_v6_SHSUB";
    check Arm_multiple_a.initial_state 227 0x1ff "arm_multiple";
    check Arm_edsp_a.initial_state 679 8388607 "arm_edsp";
    check Sum_iterative_a.initial_state 264 903 "sum_iterative";
    check Sum_recursive_a.initial_state 740 903 "sum_recursive";
    check Sum_direct_a.initial_state 18 903 "sum_direct";
    check Arm_blx2_a.initial_state 26 3 "arm_blx2";
    check Arm_cflag_a.initial_state 100 15 "arm_cflag";
    check Arm_dpi_a.initial_state 964 524287 "arm_dpi";
    check Arm_ldmstm_a.initial_state 119 7 "arm_ldmstm";
    check Arm_ldrd_strd_a.initial_state 181 255 "arm_ldrd_strd";
    check Arm_ldrstr_a.initial_state 486 0x7ffffff "arm_ldrstr";
    check Arm_mrs_a.initial_state 727 0x7ffff "arm_mrs";
    check Arm_msr_a.initial_state 639 0x1ffff "arm_msr";
    check Arm_swi_a.initial_state 45 3 "arm_swi";
    check Endian_a.initial_state 96 7 "endian";
    check Multiply_a.initial_state 130 15 "multiply";
    check Test_mem_a.initial_state 313 3 "test_mem";
  (* check Simsoc_new1_a.initial_state 190505 255 "simsoc_new1"; *)
  (* check Sorting_a.initial_state 2487176 63 "sorting"; *)
  end

let _ = (* this line with no OCaml side effect is here to be sure that ocamlbuild can compile the whole project with Sh4, without errors *)
  Sh4dec.decode, Sh0.S.simul
