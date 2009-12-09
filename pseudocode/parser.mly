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
%token UNPREDICTABLE EQ IF THEN ELSE WHILE DO ASSERT FOR TO
%token CPSR RDPLUS1
%token <Ast.processor_exception_mode> SPSR_MODE
%token <Ast.state> REG
%token <string> BIN HEX NUM
%token <string> IDENT FLAG RESERVED PROC
%token <string> NOT EVEN
%token <string> PLUS EQEQ AND LTLT MINUS EOR ROR TIMES IS IS_NOT OR

/* lowest precedence */
%left AND EOR ROR LTLT OR
%left EQEQ IS IS_NOT
%left PLUS MINUS
%left TIMES
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
| UNPREDICTABLE        { Unpredictable }
| state_range EQ exp   { Affect ($1, $3) }
| IDENT LPAR exps RPAR { Proc ($1, $3) }
| ASSERT exp           { Assert $2 }
| RESERVED items       { Misc ($1 :: $2) }
;
cond:
| IF exp THEN block                { IfThenElse ($2, $4, None) }
| IF exp THEN block ELSE block     { IfThenElse ($2, $4, Some $6) }
| WHILE exp DO block               { While ($2, $4) }
| FOR IDENT EQ NUM TO NUM DO block { For ($2, $4, $6, $8) }
;
inst:
| simple_inst SEMICOLON { $1 }
| cond                  { $1 }
;
block:
| inst            { $1 }
| BEGIN insts END { Block $2 }
;
insts:
| /* nothing */ { [] }
| inst insts    { $1 :: $2 }
;
state_range:
| state range { $1, $2 }
| IDENT FLAG  { CPSR, Flag ($1, $2) }
;
state:
| CPSR          { CPSR }
| SPSR_MODE     { SPSR $1 }
| REG           { $1 }
| IDENT         { Var $1 }
| RDPLUS1       { RdPlus1 }
;
range:
| /* nothing */           { Full }
| LSQB NUM COLON NUM RSQB { Bits ($2, $4) }
| IDENT FLAG              { Flag ($1, $2) }
| LSQB exp RSQB           { Index [$2] }
| LSQB exp COMA exps RSQB { Index ($2 :: $4) }
;
exp:
| LPAR exp RPAR            { $2 }
| NUM                      { Num $1 }
| BIN                      { Bin $1 }
| HEX                      { Hex $1 }
| state_range              { let s, r = $1 in State (s, r) }
| IF exp THEN exp ELSE exp { If ($2, $4, $6) }
| binop                    { $1 }
| NOT exp                  { Fun ($1, [$2]) }
| IDENT LPAR exps RPAR     { Fun ($1, $3) }
| IDENT EVEN               { Fun ($2, [State (Var $1, Full)]) }
| RESERVED items           { Other ($1 :: $2) }
| UNPREDICTABLE            { Other ["Unpredictable"] }
;
binop:
| exp AND exp    { BinOp ($1, $2, $3) }
| exp PLUS exp   { BinOp ($1, $2, $3) }
| exp LTLT exp   { BinOp ($1, $2, $3) }
| exp EQEQ exp   { BinOp ($1, $2, $3) }
| exp MINUS exp  { BinOp ($1, $2, $3) }
| exp EOR exp    { BinOp ($1, $2, $3) }
| exp TIMES exp  { BinOp ($1, $2, $3) }
| exp ROR exp    { BinOp ($1, $2, $3) }
| exp IS exp     { BinOp ($1, $2, $3) }
| exp IS_NOT exp { BinOp ($1, $2, $3) }
| exp OR exp     { BinOp ($1, $2, $3) }
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
| IDENT                    { $1 }
| FLAG                     { $1 }
| RESERVED                 { $1 }
| NUM                      { $1 }
| FOR                      { "for" }
| TO                       { "to" }
| LSQB IDENT COMA NUM RSQB { Printf.sprintf "[%s,%s]" $2 $4 }
;
