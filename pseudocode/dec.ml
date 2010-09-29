(**
SimSoC-Cert, a library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Functions used by the Coq generator and the C++ generator
*)

(*****************************************************************************)
(** rearrange the name *)
(*****************************************************************************)

(* In the input, each lightheader is named with one long string containing
 * special characters
 * First, we split this string in a list of words.
 * Next:
 * - for addressing modes, the function name is built by concatenating the
 *    words seperated by underscores
 * - for instructions, the function name is built by concatenating the words
 *   directly.
 *)

open Codetype;; (* from the directory "refARMparsing" *)

(*convert the name string to list*)
let str_to_lst s =
  Str.split (Str.regexp "[-:<>() \t]+") s;;

(*organise the input data with different types*)
type kind =
  | DecMode of int
  | DecInstARM
  | DecInstThumb
  | DecEncoding;;

let lightheader_to_string lh =
  let decimal b n = Printf.bprintf b "%d" n in
    match lh with
      | LH (is, s) ->
          let b = Buffer.create 80 in
            Printf.bprintf b "A%a %s" (Util.list "." decimal) is s;
            Buffer.contents b;;

(* the kind of an element *)
let add_mode (lh: lightheader) =
  match lh with
    | LH ((4 :: _ :: _ :: _), _) -> DecInstARM
    | LH ((5 :: _ :: 1 :: _), _) -> DecEncoding
    | LH ([5; n; _], _) -> DecMode n
    | LH ([7; _; _], _) -> DecInstThumb
    | LH _ -> raise (Invalid_argument ("add_mode: "^lightheader_to_string lh));;

(*catch the number of an instruction or of an addressing mode case*)
let num (lh, _) =
  match lh with LH (is, _) -> List.nth is 2;;

(* This function is used by the "params" function *)
(* rename addressing modes*)
let name (ps: maplist_element) =
  (*rename the special cases B,BL and MSR*)
  let name_lst (lh,_) =
    match lh with
      | LH (_, "B, BL") -> ["B"]
      | LH (_, "MSR  Immediate operand:") -> ["MSRimm"]
      | LH (_, "MSR  Register operand:") -> ["MSRreg"]
      | LH (_, s) ->
	  str_to_lst s
  in
  let ss = name_lst ps in
    match ss with
      | "Data" :: "processing" :: "operands" :: s -> "M1"::s
      | "Load" :: "and" :: "Store" :: "Word" :: "or" :: "Unsigned" :: "Byte" :: s -> "M2"::s
      | "Miscellaneous" :: "Loads" :: "and" :: "Stores" :: s -> "M3"::s
      | "Load" :: "and" :: "Store" :: "Multiple" :: s -> "M4"::s
      | "Load" :: "and" :: "Store" :: "Coprocessor" :: s -> "M5"::s
      | _ -> ss;;
