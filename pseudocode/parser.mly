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
%token EQ IN
%token UNPREDICTABLE UNAFFECTED
%token IF THEN ELSE WHILE DO ASSERT FOR TO CASE ENDCASE OF
%token CPSR MEMORY
%token COPROC LOAD SEND NOT_FINISHED FROM
%token <Ast.mode option> SPSR_MODE
%token <Ast.exp> REG
%token <string> BIN HEX
%token <Ast.num> NUM
%token <string> IDENT FLAG RESERVED
%token <string> NOT EVEN
%token <string> GTEQ LT GT BANGEQ AND OR BOR LSL LSR ASR
%token <string> PLUS EQEQ BAND LTLT MINUS EOR ROR STAR

/* lowest precedence */
%left AND OR
%left EQEQ BANGEQ GTEQ
%left BAND BOR EOR ROR LTLT LSL LSR ASR
%left PLUS MINUS
%left STAR
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
| IDENT prog_idents block
    { { pref = $1; pinst = $3; pname = Inst (List.hd $2, List.tl $2) } }
| IDENT operand_items MINUS operand_items block
    { { pref = $1; pinst = $5; pname = Oper ($2, $4) } }
;
prog_ident:
| prog_name prog_vars prog_version
    { { iname = $1; iparams = $2; iversion = $3 } }
;
prog_idents:
| prog_ident                  { [$1] }
| prog_ident COMA prog_idents { $1 :: $3 }
;
prog_vars:
| /* nothing */         { [] }
| LT IDENT GT prog_vars { $2 :: $4 }
;
prog_name:
| IDENT { $1 }
| BAND  { $1 }
| EOR   { $1 }
;
prog_version:
| /* nothing */ { None }
| LPAR NUM RPAR { Some $2 }
;
simple_inst:
| UNPREDICTABLE        { Unpredictable }
| exp EQ exp           { Affect ($1, $3) }
| IDENT LPAR exps RPAR { Proc ($1, $3) }
| ASSERT exp           { Assert $2 }
| RESERVED items       { Misc ($1 :: $2) }
| coproc_inst          { $1 }
;
coproc_inst:
| LOAD exp FOR coproc { Coproc ($4, "load", [$2]) }
| SEND exp TO coproc  { Coproc ($4, "send", [$2]) }
| coproc IDENT items  { Coproc ($1, $2, []) }
;
coproc:
| COPROC LSQB exp RSQB { $3 }
;
cond_inst:
| IF exp THEN block                   { If ($2, $4, None) }
| IF exp THEN block ELSE block        { If ($2, $4, Some $6) }
| WHILE exp DO block                  { While ($2, $4) }
| FOR IDENT EQ NUM TO NUM DO block    { For ($2, $4, $6, $8) }
| CASE exp OF BEGIN cases END ENDCASE { Case ($2, $5) }
;
cases:
| BIN block       { [$1, $2] }
| BIN block cases { ($1, $2) :: $3 }
;
inst:
| simple_inst           { $1 }
| simple_inst SEMICOLON { $1 }
| cond_inst             { $1 }
;
block:
| inst            { $1 }
| BEGIN insts END { Block $2 }
;
insts:
| /* nothing */ { [] }
| block insts   { $1 :: $2 }
;
simple_exp:
| NUM           { Num $1 }
| IDENT         { Var $1 }
| CPSR          { CPSR }
| UNAFFECTED    { Unaffected }
| UNPREDICTABLE { Unpredictable_exp }
| REG           { $1 }
;
exp:
| BIN                      { Bin $1 }
| HEX                      { Hex $1 }
| SPSR_MODE                { SPSR $1 }
| LPAR exp RPAR            { $2 }
| IF exp THEN exp ELSE exp { If_exp ($2, $4, $6) }
| NOT exp                  { Fun ($1, [$2]) }
| IDENT LPAR exps RPAR     { Fun ($1, $3) }
| MEMORY LSQB exp COMA NUM RSQB { Memory ($3, size_of_num $5) }
| coproc_exp               { $1 }
| binop_exp                { $1 }
| simple_exp               { $1 }
| IDENT FLAG               { Range (CPSR (*FIXME*), Flag ($1, $2)) }
| simple_exp range         { Range ($1, $2) }
| LPAR exp RPAR range      { Range ($2, $4) }
| RESERVED items           { Other ($1 :: $2) }
| simple_exp IN IDENT COMA simple_exp IN IDENT { If_exp (Var $3, $1, $5) }
;
coproc_exp:
| NOT_FINISHED LPAR coproc RPAR { Coproc_exp ($3, "NotFinished", []) }
| IDENT FROM coproc             { Coproc_exp ($3, $1, []) }
;
binop_exp:
| exp AND exp    { BinOp ($1, $2, $3) }
| exp BAND exp   { BinOp ($1, $2, $3) }
| exp PLUS exp   { BinOp ($1, $2, $3) }
| exp LTLT exp   { BinOp ($1, $2, $3) }
| exp EQEQ exp   { BinOp ($1, $2, $3) }
| exp BANGEQ exp { BinOp ($1, $2, $3) }
| exp MINUS exp  { BinOp ($1, $2, $3) }
| exp EOR exp    { BinOp ($1, $2, $3) }
| exp STAR exp   { BinOp ($1, $2, $3) }
| exp ROR exp    { BinOp ($1, $2, $3) }
| exp OR exp     { BinOp ($1, $2, $3) }
| exp BOR exp    { BinOp ($1, $2, $3) }
| exp LSL exp    { BinOp ($1, $2, $3) }
| exp LSR exp    { BinOp ($1, $2, $3) }
| exp ASR exp    { BinOp ($1, $2, $3) }
| exp GTEQ exp   { BinOp ($1, $2, $3) }
| exp LT exp     { BinOp ($1, $2, $3) }
;
range:
| LSQB NUM COLON NUM RSQB { Bits ($2, $4) }
| IDENT FLAG              { Flag ($1, $2) }
| LSQB exp RSQB           { Index $2 }
;
exps:
| /* nothing */ { [] }
| exp           { [$1] }
| exp COMA exps { $1 :: $3 }
;
items:
| /* nothing */ { [] }
| item items    { $1 :: $2 }
;
item:
| IDENT    { $1 }
| OF       { "of" }
| FLAG     { $1 }
| RESERVED { $1 }
;
operand_items:
| IDENT               { [$1] }
| COPROC              { ["Coprocessor"] }
| IDENT operand_items { $1 :: $2 }
| AND operand_items   { "and" :: $2 }
| OR operand_items    { "or" :: $2 }
;
