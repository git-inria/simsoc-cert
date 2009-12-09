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
     ["not"; "address_of"; "high"; "JE"; "IMPLEMENTATION"; "SUB"; "Jazelle";
      "CV"; "Coprocessor"; "bit_position"; "architecture"; "value_from";
      "Start"; "Coprocessor"; "load"; "send"; "first"; "second"]
     (* language keywords *)
   @ ["if", IF; "then", THEN; "else", ELSE; "begin", BEGIN; "end", END;
      "UNPREDICTABLE", UNPREDICTABLE; "Flag", FLAG "Flag"; "bit", FLAG "bit";
      "LR", REG ("14", None); "PC", REG ("15", None); "in", IN;
      "CPSR", Parser.CPSR; "AND", AND "AND"; "NOT", NOT "NOT"; "do", DO;
      "EOR", EOR "EOR"; "assert", ASSERT; "while", WHILE; "for", FOR;
      "to", TO; "Bit", FLAG "Bit"; "Rotate_Right", ROR "Rotate_Right";
      "is", IS "is"; "or", OR "or"; "is_not", IS_NOT "is_not";
      "is_even_numbered", EVEN "is_even_numbered"; "and", AND "and";
      "unaffected", UNAFFECTED; "flag", FLAG "flag"; "OR", OR "OR";
      "Logical_Shift_Left", LSL "Logical_Shift_Left";
      "Arithmetic_Shift_Right", ASR "Arithmetic_Shift_Right"]);;

}

let mode = "fiq" | "irq" | "svc" | "abt" | "und"

let digit = ['0'-'9']
let letter = ['a'-'z' 'A'-'Z' '_' '.' '\'']

let ident = letter (letter|digit)*

let reserved = "not" | "high" | "address"

let num = digit+
let bin = "0b" ['0' '1']+
let hex = "0x" ['0'-'9' 'A'-'F']+

rule token = parse
  | "/*" [^ '*']* "*/" { token lexbuf }
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
  | "==" as s { EQEQ s}
  | '+' { PLUS "+" }
  | '*' { TIMES "*" }
  | "<<" as s { LTLT s }
  | ">=" as s { GE s }
  | '-' { MINUS "-" }
  | "SPSR_" (mode as m) { SPSR_MODE (mode_of_string m) }
  | "R" (num as s) { REG (s, None) }
  | "R" (num as s) "_" (mode as m) { REG (s, Some (mode_of_string m)) }
  | "R(d+1)" { RDPLUS1 }
  | num as s { NUM s }
  | bin as s { BIN s }
  | hex as s { HEX s }
  | ident as s { try Hashtbl.find keyword_table s with Not_found -> IDENT s }
  | eof { EOF }
  | _ { raise Parsing.Parse_error }
