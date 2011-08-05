(**
SimSoC-Cert, a toolkit for generating certified processor simulators
See the COPYRIGHTS and LICENSE files.

   C code generator for processor instructions.
*)

module type GENCXX =
sig
  module G : Ast.Var with type typ = string

  module V :
  sig
    val vars_exp :
      G.typ Util.StrMap.t * 'a Util.StrMap.t ->
      Ast.exp -> G.typ Util.StrMap.t * 'a Util.StrMap.t
    val vars_exps :
      G.typ Util.StrMap.t * 'a Util.StrMap.t ->
      Ast.exp list -> G.typ Util.StrMap.t * 'a Util.StrMap.t
    val vars_inst :
      G.typ Util.StrMap.t * G.typ Util.StrMap.t ->
      Ast.inst -> G.typ Util.StrMap.t * G.typ Util.StrMap.t
    val vars_insts :
      G.typ Util.StrMap.t * G.typ Util.StrMap.t ->
      Ast.inst list -> G.typ Util.StrMap.t * G.typ Util.StrMap.t
    val vars_cases :
      G.typ Util.StrMap.t * G.typ Util.StrMap.t ->
      Ast.inst list -> G.typ Util.StrMap.t * G.typ Util.StrMap.t
    val vars :
      Ast.inst ->
      (Util.StrMap.key * G.typ) list * (Util.StrMap.key * G.typ) list
  end

  val hex_of_bin : string -> string
  val binop : string -> string
  val to_signed : Ast.exp -> Ast.exp
  val func : string -> string
  val mode : Ast.mode -> string
  val input_registers : string list
  val access_type : Ast.size -> string
  val cpsr_flag : string -> string
  val num : Buffer.t -> string -> unit
  val prog_arg : Buffer.t -> string * string -> unit
  val inreg_load : Buffer.t -> string -> unit
  val local_decl : Buffer.t -> string * string -> unit
  val mask_value : Codetype.pos_contents array -> int32 * int32
  val dec_param : (Util.StrMap.key * G.typ) list -> Ast.exp option -> Buffer.t -> Util.StrMap.key * int * int -> unit
  val lib : string -> Ast.program -> Codetype.maplist -> unit
end


module Arm6 : GENCXX = Gencxx_arm6
module Sh4 : GENCXX = Gencxx_sh4
