{
(**
SimSoC-Cert, a library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Pseudocode lexer.
*)

open Parser;;
open Ast;;
open Lexing;;

let word_of_string = int_of_string;;

let word_of_bin_string s =
  let r = ref 0 and n = String.length s in
  for i = 0 to n - 1 do
    if s.[i] = '1' then r := !r + (1 lsl (n-i))
  done;
  !r;;

let mode_of_string = function
  | "fiq" -> Fiq
  | "irq" -> Irq
  | "svc" -> Svc
  | "abt" -> Abt
  | "und" -> Und
  | _ -> invalid_arg "mode_of_string";;

}

let mode = "fiq" | "irq" | "svc" | "abt" | "und"
let num = ['0'-'9']+
let ident = ['a'-'z' 'A'-'Z' '_']+
let bin = ['0' '1']+
let binop = "==" | "and" | "+"

rule token = parse
  | [' ' '\r' '\t'] { token lexbuf }
  | '\n' { let ln = lexbuf.lex_curr_p.pos_lnum
	   and off = lexbuf.lex_curr_p.pos_cnum in
	     lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with
				      pos_lnum = ln+1; pos_bol = off };
	     token lexbuf }
  | '(' { LPAR }
  | ')' { RPAR }
  | '[' { LSQB }
  | ']' { RSQB }
  | ':' { COLON }
  | ';' { SEMICOLON }
  | '=' { EQ }
  | binop as s { BINOP s }
  | "CPSR" { Parser.CPSR }
  | "SPSR_" (mode as m) { SPSR_MODE (mode_of_string m) }
  | "R" (num as s) { REG (word_of_string s) }
  | "R" (num as s) "_" (mode as m)
      { REG_MODE (mode_of_string m, word_of_string s) }
  | num as s { WORD (word_of_string s) }
  | "0b" (bin as s) { WORD (word_of_bin_string s) }
  | ident as s { IDENT s }
