(**
SimSoC-Cert, a Coq library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the SH4 architecture following the:

SH-4, Software Manual, Renesas 32-Bit RISC, Rev.6.00 2006.09

Page numbers refer to Renesas_SH4_2006.pdf.


*)

module Cparser = struct module Cabs = Cabs end

module States = struct
  type t = 
    | Tiret
    | Pos of int
    | Range of int * int
end

module T_bit = struct
  type t = 
    | Tiret
    | Zero
    | One
    | One_Zero
    | Borrow
    | Carry
    | LSB
    | MSB
    | Overflow
    | Result_of_
    | Test
    | Underflow
    | Empty
end

type inst_code = 
  | I_0
  | I_1
  | I_n
  | I_m
  | I_i
  | I_d

type decoder_line = 
    { before_code : string
    ; inst_code : (inst_code * int) list
    ; states : States.t
    ; t_bit : T_bit.t } 

type decoder_rep = 
  | Dec_usual of decoder_line
  | Dec_dash of bool option

type dec_title = (** For the following cases, the words after "Menu" is the words we have to append (in front of the usual "Format, Summary of Operation, Instruction Code, Execution States, T Bit") to get the real title *)
  | Menu (* [ "Format" ; "Summary of Operation" ; "Instruction Code" ; "Execution States" ; "T Bit" ] *)

  (** 9.25 include to 9.47 include, 9.34 9.44 are exceptions *)
  | Menu_PR
  | Menu_NO_PR
  | Menu_NO_SZ

type decoder = 
    { dec_tab : (decoder_rep * string list) list (** *)
    ; dec_inst_ty : string
    ; dec_title : dec_title
    ; dec_title_long : string
    ; dec_other : string * string * string list }

type raw_c_code = 
    { init : string list (* WARNING [init] is unused *)
    ; code : Cparser.Cabs.definition list option (** representation of the C pseudocode, natural order : first element in the list = first line *) }

type 'a instruction = 
    { explanation_desc : string list (** information present in the part "description" *) 
    ; explanation_other : string list (** information eventually present after the C code *)


    ; decoder : decoder
    ; c_code : 'a
    ; position : int }

type 'a manual = 
    { entete : 'a (** piece of C code present at the beginning of section 9 *) 
    ; section : 'a instruction list }


(** Simplify a string (only formed with : 0, 1, n, m, i, d) into a list composed of the character and the number of occurences it appears after *)
let list_of_string_01nmid s = 
  let lg = String.length s in
  let () = match lg with 16 | 32 -> () | _ -> failwith (string_of_int lg) in
  let rec aux l n = 
    if n = lg then
      l
    else
      let rec aux2 i = 
        if n + i = lg then
          i
        else if s.[n] = s.[n + i] then
          aux2 (succ i)
        else
          i in
      let i = aux2 1 in
      aux (((match s.[n] with 
        | '0' -> I_0
        | '1' -> I_1
        | 'n' -> I_n
        | 'm' -> I_m
        | 'i' -> I_i
        | 'd' -> I_d
        | _ -> assert false (* by definition of [Str.matched_group], we can prove that this case is never reached *)
      ), let () = 
           if not (match s.[n] with '0' | '1' -> true | _ -> false) then
             match i with
                 2 | 3 (* present in floating-point instruction (from 9.25 include to 9.46 include) *) | 4 | 8 | 12 -> ()
               | _ -> failwith (Printf.sprintf "%c %d" s.[n] i)
           else
             () in
         i) :: l) (n + i) in
  aux [] 0


module String_map = Map.Make (struct type t = string let compare = compare end)
module Int_set = Set.Make (struct type t = int let compare = compare end)
