{
(**
SimSoC-Cert, a library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Pseudocode lexer.
*)

open Lexing;;
open Parser;;

let int_of_bin_string s =
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
let notneg = ['0'-'9']+
let ident = ['a'-'z' 'A'-'Z' '_']+
let bin = ['0' '1']+

rule token = parse
  | [' ' '\r' '\t'] { token lexbuf }
  | '\n' { let ln = lexbuf.lex_curr_p.pos_lnum
	   and off = lexbuf.lex_curr_p.pos_cnum in
	     lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with
				      pos_lnum = ln+1; pos_bol = off };
	     token lexbuf }
  | '=' { EQ }
  | "==" { EQEQ }
  | '(' { LPAR }
  | ')' { RPAR }
  | '[' { LSQB }
  | ']' { RSQB }
  | ':' { COLON }
  | '+' { PLUS }
  | "and" { AND }
  | "CPSR" { CPSR }
  | "SPSR_" (mode as m) { SPSR (mode_of_string m) }
  | "R" (notneg as s) { REG (int_of_string s) }
  | "R" (notneg as s) "_" mode { REG_MODE (mode_of_string m, int_of_string s) }
  | notneg as s { WORD (int_of_string s) }
  | "0b" (bin as s) { WORD (int_of_bin_string s) }
  | ident as s { IDENT s }
  | eof { raise Eof }
