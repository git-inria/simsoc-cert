%{
(**
SimSoC-Cert, a library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Pseudocode parser.
*)

  open Ast;;
%}

%token EOF
%token UNPREDICTABLE
%token EQ COLON SEMICOLON
%token CONDITION_PASSED CARRY_FROM OVERFLOW_FROM
%token IF THEN ELSE
%token <string> IDENT
%token <string> BINOP
%token LPAR RPAR LSQB RSQB
%token CPSR
%token <Ast.processor_exception_mode> SPSR_MODE
%token <Ast.processor_exception_mode * Ast.num> REG_MODE
%token <Ast.num> REG
%token <Ast.word> WORD
%token <Ast.num> NUM

%left BINOP

%type <Ast.inst> prog

%start prog

%%

prog:
| inst SEMICOLON      { $1 }
| inst SEMICOLON prog { Seq ($1, $3) }
;
inst:
| UNPREDICTABLE               { Unpredictable }
| sexp range EQ exp           { Affect ($1, $2, $4) }
| IF exp THEN prog           { IfThenElse ($2, $4, None) }
| IF exp THEN prog ELSE prog { IfThenElse ($2, $4, Some $6) }
;
sexp:
| CPSR      { CPSR }
| SPSR_MODE { SPSR $1 }
| REG       { Reg (None, Word (word_of_num $1)) }
| REG_MODE  { let m, n = $1 in Reg (Some m, Word (word_of_num n)) }
;
range:
| /* nothing */                 { All }
| LSQB NUM RSQB              { Bit $2 }
| LSQB NUM COLON NUM RSQB { Bits ($2, $4) }
exp:
| IDENT                                       { Var $1 }
| WORD                                        { Word $1 }
| sexp range                                  { State ($1, $2) }
| IF exp THEN exp ELSE exp                   { If ($2, $4, $6) }
| exp BINOP exp                               { Fun ($2, [$1; $3]) }
| IDENT LPAR exps RPAR                        { Fun ($1, $3) }
;
exps:
| /* nothing */ { [] }
| exp exps      { $1 :: $2 }
;
