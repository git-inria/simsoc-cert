(**
SimSoC-Cert, a Coq library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the SH4 architecture following the:

SH-4, Software Manual, Renesas 32-Bit RISC, Rev.6.00 2006.09

Page numbers refer to Renesas_SH4_2006.pdf.


*)

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

type 'a instruction = 
    { explanation_desc : string list (** information present in the part "description" *) 
    ; explanation_other : string list (** information eventually present after the C code *)


    ; decoder : decoder
    ; c_code : 'a
    ; position : int }

type 'a manual = 
    { entete : 'a (** piece of C code present at the beginning of section 9 *) 
    ; section : 'a instruction list }

module type C_PARSE = 
sig
  type t

  val c_of_file : string (* filename *) -> t option (* None : parsing failure *)
  val c_of_program : string (* program written in C language *) -> t option (* None : parsing failure *)
  val preprocess : string (* program written in C language *) -> string list (* program written in C language *)
  val expand_line_space : string list (* program written in C language *) -> string list (* program written in C language *) (** suppress every directive line indicating the current position and replace by the adequate number of white line instead *)

  type raw_c_code

  val organize_header : bool -> string list (* program written in C language *) -> raw_c_code
  val organize_body : bool -> string list (* program written in C language *) -> raw_c_code
  val print : out_channel -> raw_c_code -> unit
  val get_code : raw_c_code -> t option (* None : parsing failure *)
  val parse_whole : string list (* program written in C language *) -> int * int list -> string list manual -> bool (* true : arrange order *) -> raw_c_code manual
end
