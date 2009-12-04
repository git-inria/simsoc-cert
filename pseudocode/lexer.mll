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

let num_of_string = int_of_string;;
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

let flag_of_char = function
  | 'N' -> N
  | 'Z' -> Z
  | 'C' -> C
  | 'V' -> V
  | _ -> invalid_arg "flag_of_string";;

}

let mode = "fiq" | "irq" | "svc" | "abt" | "und"
let digit = ['0'-'9']
let num = digit+
let letter = ['a'-'z' 'A'-'Z' '_' '.']
let ident = letter (letter|digit)*
let bin = ['0' '1']+
let binop = "==" | "and" | "+"
let flag = ['N' 'Z' 'C' 'V']

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
  | ',' { COMA }
  | '=' { EQ }
  | "if" { IF }
  | "then" { THEN }
  | "else" { ELSE }
  | "begin" { BEGIN }
  | "end" { END }
  | "UNPREDICTABLE" { UNPREDICTABLE }
  | (flag as c) [' ' '\t']+ "Flag" { FLAG (flag_of_char c) }
  | "CPSR" { Parser.CPSR }
  | "SPSR_" (mode as m) { SPSR_MODE (mode_of_string m) }
  | "R" (num as s) { REG (None, num_of_string s) }
  | "R" (num as s) "_" (mode as m)
      { REG (Some (mode_of_string m), num_of_string s) }
  | num as s { NUM (num_of_string s) }
  | "0b" (bin as s) { WORD (word_of_bin_string s) }
  | binop as s { BINOP s }
  | ident as s { IDENT s }
  | _ { raise Parsing.Parse_error }
