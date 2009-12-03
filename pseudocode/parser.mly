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
%token EQ EQEQ COLON
%token CONDITION_PASSED CARRY_FROM OVERFLOW_FROM
%token IF THEN ELSE
%token <string> IDENT
%token LPAR RPAR LSQB RSQB
%token CPSR
%token <processor_exception_mode> SPSR_MODE
%token <processor_exception_mode * num> REG_MODE
%token <num> REG
%token <word> WORD
%token <num> NUM

%left BINOP

%type <inst> prog

%start prog

%%

prog:
| inst      { $1 }
| inst prog { Seq ($1, $2) }
;
inst:
| UNPREDICTABLE               { Unpredictable }
| sexp range EQ exp           { Affect ($1, $2, $4) }
| IF bexp THEN prog           { IfThen ($2, $4) }
| IF bexp THEN prog ELSE prog { IfThenElse ($2, $4, $6) }
;
sexp:
| CPSR      { CPSR }
| SPSR_MODE { SPSR $1 }
| REG       { Reg $1 }
| REG_MODE  { Reg $1 }
;
range:
| /* nothing */                 { All }
| LSQB NOTNEG RSQB              { Bit $2 }
| LSQB NOTNEG COLON NOTNEG RSQB { Bits ($2, $4) }
exp:
| IDENT                                       { Var $1 }
| WORD                                        { Word $1 }
| sexp range                                  { State ($1, $2) }
| IF bexp THEN exp ELSE exp                   { If ($2, $4, $6) }
| exp BINOP exp                               { Fun ($2, $1, $3) }
| IDENT LPAR exps RPAR                        { Fun ($1, $3) }
;
exps:
| /* nothing */ { [] }
| exp exps      { $1 :: $2 }
;
