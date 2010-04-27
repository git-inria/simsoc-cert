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

let mode_of_string = function
  | "fiq" -> Fiq
  | "irq" -> Irq
  | "svc" -> Svc
  | "abt" -> Abt
  | "und" -> Und
  | "usr" -> Usr
  | "sys" -> Sys
  | _ -> invalid_arg "mode_of_string";;

let keyword_table = Hashtbl.create 53;;

let _ = List.iter (fun (k, t) -> Hashtbl.add keyword_table k t)
  (List.map (fun s -> s, RESERVED s)
     (* words starting an English expression *)
     ["not"; "address_of"; "high"; "JE"; "IMPLEMENTATION"; "Jazelle"; "CV";
      "SUBARCHITECTURE"; "CPSR_with"]
     (* language keywords *)
   @ ["if", IF; "then", THEN; "else", ELSE; "begin", BEGIN; "end", END;
      "UNPREDICTABLE", UNPREDICTABLE; "Flag", FLAG "Flag"; "bit", FLAG "bit";
      "LR", REG (Reg (Num "14", None)); "PC", REG (Reg (Num "15", None));
      "pc", REG (Reg (Num "15", None)); "or", OR "or"; "and", AND "and";
      "CPSR", Parser.CPSR; "AND", BAND "AND"; "NOT", NOT "NOT"; "do", DO;
      "EOR", EOR "EOR"; "assert", ASSERT; "while", WHILE; "for", FOR;
      "to", TO; "case", CASE; "of", OF; "endcase", ENDCASE;
      "Rotate_Right", ROR "Rotate_Right"; "unaffected", UNAFFECTED;
      "flag", FLAG "flag"; "OR", BOR "OR"; "in", IN; "from", FROM;
      "Logical_Shift_Left", LSL "Logical_Shift_Left"; "Bit", FLAG "Bit";
      "Logical_Shift_Right", LSR "Logical_Shift_Right";
      "Arithmetic_Shift_Right", ASR "Arithmetic_Shift_Right";
      "SPSR", SPSR_MODE None; "Memory", MEMORY; "load", LOAD; "send", SEND;
      "Coprocessor", COPROC; "NotFinished", NOT_FINISHED]);;

let incr_line_number lexbuf =
  let ln = lexbuf.lex_curr_p.pos_lnum
  and off = lexbuf.lex_curr_p.pos_cnum in
    lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with
			     pos_lnum = ln+1; pos_bol = off };;

let register = function
  | "Register" | "Rotate" -> None
  | s -> let n = String.length s in
      if n > 1 && s.[0] = 'R' && s.[1] > 'a' && s.[1] < 'z' then
	if n <= 4 then Some (String.sub s 1 (n-1), None)
	else match String.sub s (n-4) 4 with
	  | "_fiq" -> Some (String.sub s 1 (n-5), Some Fiq)
	  | "_irq" -> Some (String.sub s 1 (n-5), Some Irq)
	  | "_svc" -> Some (String.sub s 1 (n-5), Some Svc)
	  | "_abt" -> Some (String.sub s 1 (n-5), Some Abt)
	  | "_und" -> Some (String.sub s 1 (n-5), Some Und)
	  | "_usr" -> Some (String.sub s 1 (n-5), Some Usr)
	  | "_sys" -> Some (String.sub s 1 (n-5), Some Sys)
	  | _ -> Some (String.sub s 1 (n-1), None)
      else None;;

let ident s =
  try Hashtbl.find keyword_table s
  with Not_found ->
    match register s with
      | None -> IDENT s
      | Some (n, m) -> REG (Reg (Var n, m));;

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
