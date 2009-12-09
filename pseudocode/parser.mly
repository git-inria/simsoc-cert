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

%token EOF COLON SEMICOLON COMA
%token LPAR RPAR LSQB RSQB BEGIN END
%token UNPREDICTABLE EQ IF THEN ELSE
%token CPSR
%token <Ast.processor_exception_mode> SPSR_MODE
%token <Ast.processor_exception_mode option * Ast.num> REG
%token <Ast.word> WORD
%token <Ast.num> NUM
%token <string> IDENT FLAG RESERVED PROC
%token <string> PLUS EQEQ AND LTLT NOT MINUS EOR

/* lowest precedence */
%left AND EOR
%left EQEQ
%left PLUS MINUS
%left LTLT
%nonassoc NOT
/* highest precedence */

%type <Ast.prog list> lib

%start lib /* entry point */

%%

lib:
| progs EOF { $1 }
;
progs:
| /* nothing */ { [] }
| prog progs    { $1 :: $2 }
;
prog:
| IDENT name alt_names version SEMICOLON block { ($1, $2, $4, $6) }
;
alt_names:
| /* nothing */        { }
| COMA name alt_names { }
;
name:
| IDENT { $1 }
| AND   { $1 }
| EOR   { $1 }
;
version:
| /* nothing */ { None }
| LPAR NUM RPAR { Some $2 }
;
simple_inst:
| UNPREDICTABLE                { Unpredictable }
| state_range EQ exp           { Affect ($1, $3) }
| PROC items                   { Proc ($1 :: $2) }
;
cond:
| IF exp THEN block            { IfThenElse ($2, $4, None) }
| IF exp THEN block ELSE block { IfThenElse ($2, $4, Some $6) }
;
inst:
| simple_inst SEMICOLON { $1 }
| cond                  { $1 }
;
block:
| inst  { $1 }
| BEGIN insts END { Block $2 }
;
insts:
| /* nothing */        { [] }
| inst insts { $1 :: $2 }
;
state_range:
| state range { $1, $2 }
| IDENT FLAG  { CPSR, Flag ($1, $2) }
;
state:
| CPSR          { CPSR }
| SPSR_MODE     { SPSR $1 }
| REG           { let m, n = $1 in Reg (m, n) }
| IDENT         { Var $1 }
;
range:
| /* nothing */           { Full }
| LSQB NUM RSQB           { Bit $2 }
| LSQB NUM COLON NUM RSQB { Bits ($2, $4) }
| IDENT FLAG              { Flag ($1, $2) }
;
exp:
| WORD                     { Word $1 }
| NUM                      { Word (Num $1) }
| state_range              { let s, r = $1 in State (s, r) }
| IF exp THEN exp ELSE exp { If ($2, $4, $6) }
| binop                    { $1 }
| NOT exp                  { Fun ($1, [$2]) }
| IDENT LPAR exps RPAR     { Fun ($1, $3) }
| LPAR exp RPAR            { $2 }
| RESERVED items           { Other ($1 :: $2) }
;
binop:
| exp AND exp              { BinOp ($1, $2, $3) }
| exp PLUS exp             { BinOp ($1, $2, $3) }
| exp LTLT exp             { BinOp ($1, $2, $3) }
| exp EQEQ exp             { BinOp ($1, $2, $3) }
| exp MINUS exp            { BinOp ($1, $2, $3) }
| exp EOR exp              { BinOp ($1, $2, $3) }
;
exps:
| /* nothing */ { [] }
| exp           { [$1] }
| exp COMA exps { $1 :: $3 }
;
items:
| /* nothing */  { [] }
| item items     { $1 :: $2 }
;
item:
| IDENT    { $1 }
| FLAG     { $1 }
| RESERVED { $1 }
;
