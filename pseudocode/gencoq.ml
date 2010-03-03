(**
SimSoC-Cert, a library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Coq code generator for simulation (see directory ../coq)
*)

open Ast;;
open Printf;;
open Util;;


let hex_of_bin = function
  | "0b00" | "0b0" -> "0"
  | "0b01" | "0b1" -> "1"
  | "0b10" -> "2"
  | "0b11" -> "3"
  | "0b10111" -> "abt"
  | "0b10011" -> "svc"
  | "0b10000" -> "usr"
  | "0b10001" -> "fiq"
  | "0b10010" -> "irq"
  | "0b11011" -> "und"
  | "0b11111" -> "sys"
  | _ -> "TODO";;

(*coq types of usual var*)

let type_of_val = function
  | "cond" -> "opcode"
  | "mode" -> "processor_mode"
  | "S" | "L" | "F" | "I" | "A" | "R" | "shifter_carry_out" | "shift" | "mmod"
	-> "bool"
  | "shift_operand" | "shift_imm" | "immed_8"
      -> "word"
  | _ -> "TODO";;

let cpsr_flag = function
  | "31" -> "Nbit"
  | "30" -> "Zbit"
  | "29" -> "Cbit"
  | "28" -> "Vbit"
  | "27" -> "Qbit"
  | "24" -> "Jbit"
  | "9" -> "Ebit"
  | "8" -> "Abit"
  | "7" -> "Ibit"
  | "6" -> "Fbit"
  | "5" -> "Tbit"
  | _ -> "TODO";;

let reg_id = function
  | "15" -> PC
  | "14" -> LR
  | "13" -> SP
  | n -> n;;

let func = function
  | "address of the instruction after the BLX instruction"
  | "address_of_the_instruction_after_the_branch_instruction"
  | "address_of_instruction_after_the_BLX_instruction"
  | "address_of_next_instruction_after_the_SWI_instruction"
    -> " next_inst_address";;

let binop = function
  | "AND" -> "and"
  | "OR" -> "or"
  | "EOR" -> "xor"
  | "NOT" -> "not"
  | "and" -> "&&"
  | "or" -> "||"
  | "Logical_Shift_Left" | "<<" -> "Logical_Shift_Left"
  | "Logical_Shift_Right"| ">>" -> "Logical_Shift_Right"
  | "Arithmetic_Shift_Right" -> "Arithmetic_Shift_Right"
  | "Rotate_Right" -> "Rotate_right"
  | _ -> "TODO";;
