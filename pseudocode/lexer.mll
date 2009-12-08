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
  (List.map (fun s -> s, RESERVED s) ["not"; "address"; "high"; "JE"]
   @ ["if", IF; "then", THEN; "else", ELSE; "begin", BEGIN; "end", END;
      "UNPREDICTABLE", UNPREDICTABLE; "Flag", FLAG true; "bit", FLAG false;
      "LR", REG (None, 14); "PC", REG (None, 15); "and", AND "and";
      "CPSR", Parser.CPSR; "AND", AND "AND"; "NOT", NOT "NOT"]);;

}

let mode = "fiq" | "irq" | "svc" | "abt" | "und"

let digit = ['0'-'9']
let letter = ['a'-'z' 'A'-'Z' '_' '.' '-']

let ident = letter (letter|digit)*

let reserved = "not" | "high" | "address"

let num = digit+
let bin = "0b" ['0' '1']+
let hex = "0x" ['0'-'9' 'A'-'F']+

rule token = parse
  | "/*" _* "*/" { token lexbuf }
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
  | "SPSR_" (mode as m) { SPSR_MODE (mode_of_string m) }
  | "R" (num as s) { REG (None, num_of_string s) }
  | "R" (num as s) "_" (mode as m)
      { REG (Some (mode_of_string m), num_of_string s) }
  | bin as s { WORD (Bin (String.length s - 2, num_of_string s)) }
  | hex as s { WORD (Hex (word_of_string s)) }
  | num as s { NUM (num_of_string s) }
  | "==" as s { EQEQ s }
  | "+" { PLUS "+" }
  | "<<" as s { LTLT s }
  | ident as s { try Hashtbl.find keyword_table s with Not_found -> IDENT s }
  | eof { EOF }
  | _ { raise Parsing.Parse_error }
