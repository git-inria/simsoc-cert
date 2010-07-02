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

let keyword_table = Hashtbl.create 53;;

List.iter (fun (k, t) -> Hashtbl.add keyword_table k t) [
  (* instructions *)
  "begin", BEGIN; "end", END; "if", IF; "then", THEN; "else", ELSE;
  "while", WHILE; "for", FOR; "to", TO; "do", DO;
  "case", CASE; "of", OF; "endcase", ENDCASE;
  "assert", ASSERT; "UNPREDICTABLE", UNPREDICTABLE;
  (* registers *)    
  "Flag", FLAG "Flag"; "flag", FLAG "flag"; "bit", FLAG "bit";
  "Bit", FLAG "Bit"; "CPSR", Parser.CPSR; "SPSR", Parser.SPSR;
  "LR", REGNUM "14"; "PC", REGNUM "15"; "R", REG; "GE", GE;
  "Rd", REGVAR "d"; "RdHi", REGVAR "dHi"; "RdLo", REGVAR "dLo";
  "Rs", REGVAR "s"; "Rm", REGVAR "m"; "Rn", REGVAR "n"; "Ri", REGVAR "i";
  (* modes *) 
  "_fiq", MODE Fiq; "_irq", MODE Irq; "_svc", MODE Svc; "_abt", MODE Abt;
  "_und", MODE Und; "_usr", MODE Usr; "_sys", MODE Sys;
  (* conditions *)
  "or", OR "or"; "and", AND "and"; "in", IN;
  (* binary operators *)
  "AND", BAND "AND"; "NOT", NOT "NOT"; "EOR", EOR "EOR";
  "Rotate_Right", ROR "Rotate_Right"; "OR", BOR "OR";
  "Logical_Shift_Left", LSL "Logical_Shift_Left";
  "Logical_Shift_Right", LSR "Logical_Shift_Right";
  "Arithmetic_Shift_Right", ASR "Arithmetic_Shift_Right";
  (* memory *)
  "Memory", MEMORY;
  (* coprocessors *)
  "Coprocessor", COPROC; "load", LOAD; "send", SEND; "from", FROM;
  "NotFinished", NOT_FINISHED;
  (* other expressions *)
  "unaffected", UNAFFECTED];;

let incr_line_number lexbuf =
  let ln = lexbuf.lex_curr_p.pos_lnum
  and off = lexbuf.lex_curr_p.pos_cnum in
    lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with
			     pos_lnum = ln+1; pos_bol = off };;

let ident s =
  try Hashtbl.find keyword_table s with Not_found -> IDENT s;;

}

let digit = ['0'-'9']
let letter = ['a'-'z' 'A'-'Z']
let char = letter | digit
let sep = '.' | '_'
let char_sep = char | sep

let ident = "R" | 'R' letter | 'R' letter char char_sep*
  | (letter # ['R' 'S']) char_sep*
  | "S" | "SPSR" | 'S' (letter # 'P') char_sep* 
  | '_' char_sep*

let num = digit+
let bin = "0b" ['0' '1']+
let hex = "0x" ['0'-'9' 'A'-'F' 'a'-'f']+

rule token = parse
  | "//" { one_line_comment lexbuf }
  | "/*" { multi_line_comment lexbuf }
  | '\n' { incr_line_number lexbuf; token lexbuf }
  | [' ' '\r' '\t'] { token lexbuf }
  | '(' { LPAR }
  | ')' { RPAR }
  | '[' { LSQB }
  | ']' { RSQB }
  | ':' { COLON }
  | ';' { SEMICOLON }
  | ',' { COMA }
  | '=' { EQ }
  | '+' { PLUS "+" }
  | '*' { STAR "*" }
  | '-' { MINUS "-" }
  | '<' { LT "<" }
  | '>' { GT ">" }
  | "==" as s { EQEQ s}
  | "<<" as s { LTLT s }
  | ">=" as s { GTEQ s }
  | "!=" as s { BANGEQ s }
  | num as s { NUM s }
  | bin as s { BIN s }
  | hex as s { HEX s }
  | ident as s { ident s }
  | eof { EOF }
  | _ { raise Parsing.Parse_error }

and multi_line_comment = parse
  | '\n' { incr_line_number lexbuf; multi_line_comment lexbuf }
  | "*/" { token lexbuf }
  | _ { multi_line_comment lexbuf }

and one_line_comment = parse
  | '\n' { token lexbuf }
  | _ { one_line_comment lexbuf }
