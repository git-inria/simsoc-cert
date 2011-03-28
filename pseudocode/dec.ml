(**
SimSoC-Cert, a toolkit for generating certified processor simulators
See the COPYRIGHTS and LICENSE files.

Functions common to the decoder generators.
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
open Lightheadertype;; (* from the directory "refARMparsing" *)

(*convert the name string to list*)
let str_to_lst s =
  Str.split (Str.regexp "[-:<>() \t]+") s;;

(*organise the input data with different types*)
type kind =
  | DecMode of int
  | DecInstARMCond
  | DecInstARMUncond
  | DecInstThumb
  | DecEncoding;;

let lightheader_to_string lh =
  let decimal b n = Printf.bprintf b "%d" n in
    match lh with
      | LH (is, s) ->
          let b = Buffer.create 80 in
            Printf.bprintf b "A%a %s" (Util.list "." decimal) is s;
            Buffer.contents b;;

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

module type DEC = 
sig
  (* the kind of an element *)
  val add_mode : Lightheadertype.lightheader -> kind
  val gen_pattern_get_array : 'a array -> 'a array
  val word_size : string
  val specific_uncond_inst : Lightheadertype.lightheader -> bool
  val prefix_proc : string
  val prefix_inst : string
  val display_cond : bool
  val decode_body : string list
  val sort_inst : (Lightheadertype.lightheader * 'a) list -> (Lightheadertype.lightheader * 'a) list
  val nb_buff : int
end

module Arm : DEC =
struct
  let add_mode (lh: lightheader) =
    match lh with
      | LH ((4 :: 1 :: (8|16|45|59|67|90) :: _), _) -> DecInstARMUncond
      | LH ((4 :: _ :: _ :: _), _) -> DecInstARMCond
      | LH ((5 :: _ :: 1 :: _), _) -> DecEncoding
      | LH ([5; n; _], _) -> DecMode n
      | LH ([7; _; _], _) -> DecInstThumb
      | LH _ -> raise (Invalid_argument ("add_mode: "^lightheader_to_string lh));;

  let twenty_height = 28
  let gen_pattern_get_array x = Array.sub x 0 twenty_height
  let word_size = string_of_int twenty_height
  let specific_uncond_inst _ = true

  let prefix_proc = "Arm_"
  let prefix_inst = "arm6inst"
  let display_cond = true  
  let decode_body =
    [ "(w : word) : decoder_result inst :="
    ; "  match w32_first4bits_of_word w with"
    ; "    | word4 1 1 1 1 => decode_unconditional w"
    ; "    | _ => decode_conditional w"
    ; "  end." ]

  (* Numbers in pattern refers to instruction number, i.e.,
   * the subsection in which the instruction is defined *)
  let order_inst p =
    match num p with
      | 45|8|59|67|16|90 -> -6 (* instruction without condition *)
      | 84|85|86|87|88|89|129|113|114|115|146|147|148 -> -1 (* instructions without accumulator *)
      | 9|10|11|13|39|40 -> 1 (* v5 instructions with SBO or SBZ can hide other v6 instructions *)
      | 25|105|31|101 -> 2 (* loadstore instructions with a 'T' *)
      | 28|102|104|30|26|29 -> 3
      | 38 -> 4
      | 19|20|21|22|96|97|98|35|106|116|117|99|100|23|24|41
      | 42|65|18|60|61|2|3|4|6|14|15 -> 5 (* other instuctions with a mode*)
      | _ -> 0;;
  let sort_inst l = List.sort (fun a b -> order_inst a - order_inst b) l
  let nb_buff = 5
end

module Sh4 : DEC = 
struct
  let add_mode _ = DecInstARMUncond
  let gen_pattern_get_array x = x
  let word_size = "16"

  let specific_uncond_inst = function 
    | LH (_ :: n :: _, _) -> C2pc.is_not_float_mmu n
    | LH _ -> true

  let prefix_proc = "Sh4_"
  let prefix_inst = "sh4inst"
  let display_cond = false
  let decode_body = [ ":= decode_unconditional." ]
  let sort_inst x = x
  let nb_buff = 0
end
