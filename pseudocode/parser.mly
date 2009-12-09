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
%token UNPREDICTABLE EQ IF THEN ELSE WHILE DO ASSERT FOR TO UNAFFECTED IN
%token CPSR RDPLUS1
%token <Ast.processor_exception_mode> SPSR_MODE
%token <Ast.num * Ast.processor_exception_mode option> REG
%token <string> BIN HEX
%token <Ast.num> NUM
%token <string> IDENT FLAG RESERVED PROC
%token <string> NOT EVEN GE
%token <string> PLUS EQEQ AND LTLT MINUS EOR ROR TIMES IS IS_NOT OR LSL ASR

/* lowest precedence */
%left AND EOR ROR LTLT OR LSL ASR GE
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
| /* nothing */       { }
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
| exp EQ exp           { Affect ($1, $3) }
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
simple_exp:
| NUM           { Num $1 }
| IDENT         { Var $1 }
| CPSR          { CPSR }
| UNAFFECTED    { Unaffected }
| UNPREDICTABLE { UnpredictableValue }
;
exp:
| simple_exp               { $1 }
| LPAR exp RPAR            { $2 }
| BIN                      { Bin $1 }
| HEX                      { Hex $1 }
| IF exp THEN exp ELSE exp { If ($2, $4, $6) }
| binop                    { $1 }
| NOT exp                  { Fun ($1, [$2]) }
| IDENT LPAR exps RPAR     { Fun ($1, $3) }
| IDENT EVEN               { Fun ($2, [Var $1]) }
| SPSR_MODE                { SPSR $1 }
| REG                      { Reg $1 }
| RDPLUS1                  { RdPlus1 }
| IDENT FLAG               { Range (CPSR, Flag ($1, $2)) }
| simple_exp range         { Range ($1, $2) }
| LPAR exp RPAR range      { Range ($2, $4) }
| RESERVED items           { Other ($1 :: $2) }
| simple_exp IN IDENT COMA simple_exp IN IDENT { If (Var $3, $1, $5) }
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
| exp LSL exp    { BinOp ($1, $2, $3) }
| exp ASR exp    { BinOp ($1, $2, $3) }
| exp GE exp     { BinOp ($1, $2, $3) }
;
range:
| LSQB NUM COLON NUM RSQB { Bits ($2, $4) }
| IDENT FLAG              { Flag ($1, $2) }
| LSQB exp RSQB           { Index [$2] }
| LSQB exp COMA exps RSQB { Index ($2 :: $4) }
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
| IN                       { "in" }
| LSQB IDENT COMA NUM RSQB { Printf.sprintf "[%s,%s]" $2 $4 }
;
