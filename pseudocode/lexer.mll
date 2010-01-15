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

let num_of_string s = Scanf.sscanf s "%i" (fun x -> x);;

let word_of_string s = Scanf.sscanf s "%li" (fun x -> x);;

let mode_of_string = function
  | "fiq" -> Fiq
  | "irq" -> Irq
  | "svc" -> Svc
  | "abt" -> Abt
  | "und" -> Und
  | _ -> invalid_arg "mode_of_string";;

let keyword_table = Hashtbl.create 53;;

let _ = List.iter (fun (k, t) -> Hashtbl.add keyword_table k t)
  (List.map (fun s -> s, RESERVED s)
     (* words starting an English expression *)
     ["not"; "address_of"; "high"; "JE"; "IMPLEMENTATION"; "Jazelle";
      "CV"; "bit_position"; "architecture"; "SUBARCHITECTURE";
      "Start"; "CPSR_with"; "ARMv5"]
     (* language keywords *)
   @ ["if", IF; "then", THEN; "else", ELSE; "begin", BEGIN; "end", END;
      "UNPREDICTABLE", UNPREDICTABLE; "Flag", FLAG "Flag"; "bit", FLAG "bit";
      "LR", REG (Reg (Num "14", None)); "PC", REG (Reg (Num "15", None));
      "pc", REG (Reg (Num "15", None)); "or", OR "or"; "and", AND "and";
      "CPSR", Parser.CPSR; "AND", BAND "AND"; "NOT", NOT "NOT"; "do", DO;
      "EOR", EOR "EOR"; "assert", ASSERT; "while", WHILE; "for", FOR;
      "to", TO; "Bit", FLAG "Bit"; "Rotate_Right", ROR "Rotate_Right";
      "unaffected", UNAFFECTED; "flag", FLAG "flag"; "OR", BOR "OR";
      "Logical_Shift_Left", LSL "Logical_Shift_Left"; "in", IN;
      "Arithmetic_Shift_Right", ASR "Arithmetic_Shift_Right"; "from", FROM;
      "SPSR", SPSR_MODE None; "Memory", MEMORY; "load", LOAD; "send", SEND;
      "Coprocessor", COPROC; "NotFinished", NOT_FINISHED]);;

let incr_line_number lexbuf =
  let ln = lexbuf.lex_curr_p.pos_lnum
  and off = lexbuf.lex_curr_p.pos_cnum in
    lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with
			     pos_lnum = ln+1; pos_bol = off };;

let is_register s = s <> "" && s.[0] = 'R';;

let ident s =
  try Hashtbl.find keyword_table s
  with Not_found ->
    if is_register s then
      let s = String.sub s 1 (String.length s - 1) in
	REG (Reg (Var s, None))
    else IDENT s

}

let mode = "fiq" | "irq" | "svc" | "abt" | "und"

let digit = ['0'-'9']
let letter = ['a'-'z' 'A'-'Z' '_' '.']

let ident = letter (letter|digit)*

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
  | "SPSR_" (mode as m) { SPSR_MODE (Some (mode_of_string m)) }
  | "R" (num as s) { REG (Reg (Num s, None)) }
  | "R" (num as s) "_" (mode as m)
      { REG (Reg (Num s, Some (mode_of_string m))) }
  | num as s { NUM s }
  | bin as s { BIN s }
  | hex as s { HEX s }
  | ident as s { try Hashtbl.find keyword_table s with Not_found -> IDENT s }
  | eof { EOF }
  | _ { raise Parsing.Parse_error }

and multi_line_comment = parse
  | '\n' { incr_line_number lexbuf; multi_line_comment lexbuf }
  | "*/" { token lexbuf }
  | _ { multi_line_comment lexbuf }

and one_line_comment = parse
  | '\n' { token lexbuf }
  | _ { one_line_comment lexbuf }
