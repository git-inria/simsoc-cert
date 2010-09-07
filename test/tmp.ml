#directory "../extract/tmp";;
#load "extract.cma";;
#load "sum_recursive.cmo";;

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
open Sum_recursive

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

let compute_state n =
  let _, r = S.simul initial_state (nat n) in
    match r with
      | SimOk s -> s
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
