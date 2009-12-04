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
%token EQ COLON SEMICOLON COMA
%token CONDITION_PASSED CARRY_FROM OVERFLOW_FROM
%token IF THEN ELSE
%token <string> IDENT
%token <string> BINOP
%token LPAR RPAR LSQB RSQB BEGIN END
%token CPSR
%token <Ast.processor_exception_mode> SPSR_MODE
%token <Ast.processor_exception_mode option * Ast.num> REG
%token <Ast.word> WORD
%token <Ast.num> NUM
%token <Ast.flag> FLAG

%left BINOP

%type <Ast.prog list> lib

%start lib

%%

lib:
| prog EOF { $1 }
;
prog:
| /* nothing */                   { [] }
| IDENT IDENT SEMICOLON inst prog { ($1, $2, $4) :: $5 }
;
insts:
| /* nothing */        { [] }
| inst                 { [$1] }
| inst SEMICOLON insts { $1 :: $3 }
;
inst:
| BEGIN insts END            { Block $2 }
| UNPREDICTABLE              { Unpredictable }
| sexp EQ exp                { Affect ($1, None, $3) }
| sexp range EQ exp          { Affect ($1, Some $2, $4) }
| IF exp THEN inst           { IfThenElse ($2, $4, None) }
| IF exp THEN inst ELSE inst { IfThenElse ($2, $4, Some $6) }
;
sexp:
| CPSR      { CPSR }
| SPSR_MODE { SPSR $1 }
| REG       { let m, n = $1 in Reg (m, n) }
| IDENT     { Var $1 }
| FLAG      { Flag $1 }
;
range:
| LSQB NUM RSQB           { Bit $2 }
| LSQB NUM COLON NUM RSQB { Bits ($2, $4) }
exp:
| WORD                     { Word $1 }
| NUM                      { Word (word_of_num $1) }
| sexp                     { State $1 }
| sexp range               { Range (State $1, $2) }
| IF exp THEN exp ELSE exp { If ($2, $4, $6) }
| exp BINOP exp            { Fun ($2, [$1; $3]) }
| IDENT LPAR exps RPAR     { Fun ($1, $3) }
| idents                   { Other $1 }
;
exps:
| /* nothing */ { [] }
| exp           { [$1] }
| exp COMA exps { $1 :: $3 }
;
idents:
| IDENT IDENT  { [$1; $2] }
| IDENT idents { $1 :: $2 }
;
