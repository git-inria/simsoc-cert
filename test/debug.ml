#directory "../extract/tmp";;
#load "extract.cma";;

open Arm
open BinInt
open BinPos
open Bitvec
open Datatypes
open Integers
open Proc
open SCC
open Simul
open State
open Util
open Arm6
open Ascii
open String0
open Semantics
open Functions

exception SimKO;;

let nat =
 let rec aux = function
   | 0 -> O
   | k -> S (aux (k-1))
 in fun k ->
   if k < 0 then invalid_arg "not a nat"
   else aux k;;

let rec positive = function
 | x when x <= 0 -> invalid_arg "not a positive"
 | 1 -> Coq_xH
 | x when x mod 2 = 0 -> Coq_xO (positive (x/2))
 | x -> Coq_xI (positive (x/2));;

let coq_Z = function
 | 0 -> Z0
 | x when x < 0 -> Zneg (positive (-x))
 | x -> Zpos (positive x);;

let simul s n =
  let _, r = S.simul s (nat n) in
    match r with
      | SimOk s -> s
      | _ -> raise SimKO;;

let next_state s =
  let _, r = S.simul s (nat 1) in
    match r with
      | SimOk s' -> s'
      | _ -> raise SimKO;;

let rec positive_to_int = function
  | Coq_xH -> 1
  | Coq_xO p -> 2*(positive_to_int p)
  | Coq_xI p -> 2*(positive_to_int p)+1;;

let coq_Z_to_int = function
  | Z0 -> 0
  | Zneg p -> -(positive_to_int p)
  | Zpos p -> positive_to_int p;;

let get_reg s n = coq_Z_to_int ((Proc.reg (State.proc s)) (R (coq_Z n)));;

let read_word s a =
  coq_Z_to_int (read s (coq_Z a) Bitvec.Word);;

let rec read_words s a n =
  if n = 0 then []
  else read_word s a :: read_words s (a+4) (n-1);;

(* current instruction *)
let instr s =
  Arm6dec.decode (read s (address_of_current_instruction s) Word);;

(* display the stack *)
let stack s =
  let stack_top = 0xff000 in (* value given in common.h*)
  let sp = get_reg s 13 in
    if (sp>stack_top) then raise SimKO
    else read_words s sp ((stack_top-sp)/4);;

let fp=11 and sp=13 and lr=14 and pc=15;;

let data_coqstr = (String ((Ascii (false, false, true, false, false,
              true, true, false)), (String ((Ascii (true, false, false,
              false, false, true, true, false)), (String ((Ascii (false,
              false, true, false, true, true, true, false)), (String ((Ascii
              (true, false, false, false, false, true, true, false)),
              EmptyString))))))));;

let check state steps expected name =
  let s = simul state steps in
    if get_reg s 0 = expected then print_endline (name^" OK.")
    else (
      print_string ("Error in "^name^", r0 = ");
      print_int (get_reg s 0); print_string " instead of ";
      print_int expected; print_endline "."
    );;

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
