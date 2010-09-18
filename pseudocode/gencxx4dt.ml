(**
SimSoC-Cert, a library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Generate additional C/C++ code for implementing dynamic translation in Simlight.
*)

open Ast;;
open Printf;;
open Util;;
open Dec;;
open Codetype;;

let out b (i,_) =
  (* TODO ... *)
  bprintf b "/* %s */" i.pref;;

(* main function
 * bn: output file basename, pcs: pseudo-code trees, decs: decoding rules *)
let lib (bn: string) (pcs: prog list) (decs: Codetype.maplist) =
  let pcs' = List.map Gencxx.lsm_hack pcs in (* hack LSM instructions *)
  let pds: (prog*maplist_element) list = Flatten.flatten pcs' decs in
    (* create buffers for header file (bh) and source file (bc) *)
  let bh = Buffer.create 10000 and bc = Buffer.create 10000 in
    bprintf bh "/* header file */\n";
    bprintf bh "%a\n" (list "\n" out) pds;
    bprintf bc "/* source file */\n";
    (* write buffers to files *)
    let outh = open_out (bn^".h") and outc = open_out (bn^".c") in
      Buffer.output_buffer outh bh; close_out outh;
      Buffer.output_buffer outc bc; close_out outc;;
