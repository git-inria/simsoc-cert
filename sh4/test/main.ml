(*
SimSoC-Cert, a toolkit for generating certified processor simulators
See the COPYRIGHTS and LICENSE files
*)

open BinInt
open BinPos
open Bitvec
open Datatypes

let str_of_msg = 
  let open Sh4_Message in
  function
  | InvalidInstructionSet -> "InvalidInstructionSet"
  | DecodingReturnsUnpredictable -> "DecodingReturnsUnpredictable"
  | Case -> "Case"
  | ComplexSemantics -> "ComplexSemantics"

module type TEST = 
sig
  val main : unit -> (string (* function name *) * float (* exectution time *)) list * float (* max execution time *) * float (* total time *)
end

module type SH4DEC = module type of Sh4_Dec

module Sh_Test (Sh4_Dec : SH4DEC) : TEST =
struct
  type state = Sh4_State.state

let simul lbs = 
  let n = Camlcoq.camlint_of_nat (Sh4_Simul.Simu.nb_next lbs) in
  Sh4_Simul.Simu.catch Sh4_Simul.S.simul (fun m lbs ->
    let num = Sh4_Simul.Simu.nb_next lbs in
    let step = string_of_int (n - Camlcoq.camlint_of_nat num) in
    failwith ("SimKo: " ^ str_of_msg m ^ " at step " ^ step)) lbs;;

let next = 
  Sh4_Simul.Simu.bind (fun lbs -> Sh4_Simul.Simu.SimOk ((), { lbs with Sh4_Simul.Simu.nb_next = n1 }))
    (fun () -> simul);;

let (+) = Int32.add
let (-) = Int32.sub
let (/) = Int32.div

let regz s n = Sh4_Proc.reg (Sh4_State.proc s) ((*Sh4.R*) (Camlcoq.z_of_camlint n));;
let reg s n = Camlcoq.camlint_of_coqint (regz s n);;

let read_z s a = Sh4_State.read s (Camlcoq.z_of_camlint a) Bitvec.Word;;
let read_word s a = Camlcoq.camlint_of_z (read_z s a);;

let rec read_words s a n =
  if n = 0_l then []
  else read_word s a :: read_words s (a+4_l) (n-1_l);;

(* current instruction *)
let instr s =
  Sh4_Dec.decode (Sh4_State.read s (Sh4_State.address_of_current_instruction s) Word);;

(* display the stack *)
let stack s =
  let stack_top = 0xff000_l in (* value given in common.h*)
  let sp = reg s 13_l in
    if (sp>stack_top) then Pervasives.raise (Failure "stack pointer above stack")
    else read_words s sp ((stack_top-sp)/4_l);;

let return a lbs = Sh4_Simul.Simu.SimOk (a, lbs)

let mk_st state steps = 
  { Sh4_Simul.Simu.semst = { Sh4_Functions.Semantics.S.loc = [] ; bo = true ; st = state } ; nb_next = Camlcoq.nat_of_camlint steps }

let get_st f x = f x.Sh4_Simul.Simu.semst.Sh4_Functions.Semantics.S.st x

let check state steps expected name =
  try
    ignore (Sh4_Simul.Simu.bind simul (fun () -> get_st (fun s -> 
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

let run_opt (max : int32 option) : (BinInt.coq_Z * (int32 * hexa) list) Sh4_Simul.Simu.simul_semfun =
  let rec aux : (int32 * hexa) list -> (int32 * hexa) list Sh4_Simul.Simu.simul_semfun = function
    | (step, Ox pc) :: l' as l ->
      if Some step = max then return l
      else
        Sh4_Simul.Simu.bind Sh4_Simul.Simu.conjure_up_true (fun () -> 
        Sh4_Simul.Simu.bind next (fun () -> 
        get_st (fun s' -> 
        let pc' = (reg s' 15_l) - 8_l in
        (if pc' = pc then return
         else if pc' = pc+4_l then aux
         else function x :: xs -> aux (x :: x :: xs) | _ -> assert false)
          ((step+1_l, Ox pc') :: l')
       )))
    | _ -> Pervasives.raise (Failure "inside run function")
  in 

  Sh4_Simul.Simu.bind (get_st (fun s0 -> aux [ (0_l, Ox ((reg s0 15_l) - 8_l))
                                           ; (0_l, Ox ((reg s0 15_l) - 8_l))]))
    (fun l -> 
      get_st (fun sn -> return (regz sn 0_l, l)));;

let run s0 = run_opt None (mk_st s0 1_l);;
let runmax s0 max = run_opt (Some max) (mk_st s0 1_l);;

let main () =
  let check f n1 n2 = check f (Int32.of_int n1) (Int32.of_int n2) in
  let l = 
    [ (*check Sum_iterative_a.initial_state 264 903, "sum_iterative"
    ; *)check Sum_recursive_a.initial_state 740 903, "sum_recursive"
    ; check Sum_direct_a.initial_state 18 903, "sum_direct"
    ; check Endian_a.initial_state 96 7, "endian"
    ; check Multiply_a.initial_state 130 15, "multiply"
    ; check Test_mem_a.initial_state 313 3, "test_mem"
 (* ; check Simsoc_new1_a.initial_state 190505 255, "simsoc_new1" *)
 (* ; check Sorting_a.initial_state 2487176 63, "sorting" *) ] in
  let max_length = List.fold_left (fun m (_, s) -> max m (String.length s)) 0 l in
  
  List.fold_left (fun (acc, max_t, total) (f, s) -> 
    let s = Printf.sprintf "%s%s" s (String.make (Pervasives.(-) max_length (String.length s)) ' ') in
    let f_init = Unix.gettimeofday () in
    let () = f s in
    let t = Unix.gettimeofday () -. f_init in
    (s, t) :: acc, max max_t t, total +. t) ([], min_float, 0.) l
end

open Printf

let green = sprintf "\x1B\x5B32m%s\x1B\x5B39m"

let _ = 
  let l = 
    [ (*"sh4mldec", (module Sh4mldec : SH4DEC)
    ; *)"sh4dec", (module Sh4_Dec : SH4DEC) ] in

  let (*[ n1, l1, t_max1
      ; n2, l2, t_max2 ] *)
      l_tot
      = 
    List.map (fun (name, m) -> 
      let () = printf "(* test of module %s *)\n%!" name in 
      let l, t_max, t_all = 
        let module M = Sh_Test ((val m : SH4DEC)) in M.main () in
      let () = printf "(*   total : %.04f seconds *)\n%!" t_all in
      name, List.rev l, t_max) l in

  begin
    List.iter (fun (n, _, _) -> printf "%s " n) l_tot;
    printf "\n";
(*    List.iter2 (
      let f t_max = String.length (sprintf "%.04f" t_max) in
      let t_max1, t_max2 = f t_max1, f t_max2 in
      fun (s, t1) (_, t2) -> 
        let i b0 t t_max = 
          let s = sprintf "%.04f" t in
          sprintf "%s%s" (String.make (t_max - (String.length s)) ' ') ((if t1 > t2 = b0 then green else fun x -> x) s) in
        printf "%s %s %s\n" s (i false t1 t_max1) (i true t2 t_max2)
    ) l1 l2;*)
  end
