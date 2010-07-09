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



let gen_param1 _x = ();;

let gen_param1s _x = ();;

let gen_range _x = ();;  

let gen_bin x =
  let dec b ls =
    match ls with
      | Value s -> 
	  begin match s with
	    | true -> string b "1"
	    | false -> string b "0"
	  end 
      | Shouldbe s -> 
	  begin match s with
	    | true -> string b "1" 
	    | false -> string b "0"
	  end
      | Param1 _ -> bprintf b "%d" (Random.int 1)
      | Param1s _ -> bprintf b "%d" (Random.int 1)
      | Range _ -> bprintf b "%d" (Random.int 1)
      | Nothing -> ()
  in
  let aux b =
    let lst = Array.to_list x in
      (list "" dec) b (List.rev lst)
  in aux;;

let bin_inst b (lh, ls) =
  let md = add_mode (name (lh,ls)) in
      match md with
	| DecInst -> 
	    bprintf b "%t\n" (gen_bin ls)
	| DecEncoding -> ()
	| DecMode _ -> ()
;;

(*let gen_head = 
  let hd = 7F454C4601010161000000000000000002 in
  let oc = open_out_bin "string" in
    output_byte oc hd;
    close_out oc;;*)

let gen_test b ps =
  (*gen_head;*)
  (list "" bin_inst) b ps;;
