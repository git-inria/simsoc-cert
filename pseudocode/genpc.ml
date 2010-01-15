(**
SimSoC-Cert, a library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Pseudocode pretty-printer.
*)

open Ast;;
open Printf;;
open Util;;

let rec indent b i = if i > 0 then bprintf b " %a" indent (i-1);;

let string_of_mode = function
  | Fiq -> "fiq"
  | Irq -> "irq"
  | Svc -> "svc"
  | Abt -> "abt"
  | Und -> "und";;

let mode b m = string b (string_of_mode m);;

let num = string;;

let level = function
  | "and" -> 0
  | "==" | "!=" | "is" | "is_not" | ">=" | "<" -> 1
  | "+" | "-" -> 2
  | _ -> -1;;

let rec exp b = function
  | Bin s | Hex s | Num s -> string b s
  | If (e1, e2, e3) -> bprintf b "if %a then %a else %a" exp e1 exp e2 exp e3
  | BinOp (_, f, _) as e -> pexp_level (level f) b e
  | Fun (("is_even_numbered" as f), [e]) -> bprintf b "%a %s" exp e f
  | Fun (f, es) -> bprintf b "%s(%a)" f (list ", " exp) es
  | Other ss -> list " " string b ss
  | CPSR -> string b "CPSR"
  | SPSR None -> string b "SPSR"
  | SPSR (Some m) -> bprintf b "SPSR_%a" mode m
  | Reg (Num "14", None) -> string b "LR"
  | Reg (e, o) -> bprintf b "R%a%a" exp e (option "_" mode) o
  | Var s -> string b s
  | Range (CPSR, (Flag _ as r)) -> bprintf b "%a" range r
  | Range (e, (Flag _ as r)) -> bprintf b "%a %a" pexp e range r
  | Range (e, r) -> bprintf b "%a%a" pexp e range r
  | UnpredictableValue -> string b "UNPREDICTABLE"
  | Unaffected -> string b "unaffected"
  | Memory (e, n) -> bprintf b "Memory[%a,%a]" exp e num n
  | Coproc_exp (e, "NotFinished", _) -> bprintf b "NotFinished(%a)" coproc e
  | Coproc_exp (e, s, _) -> bprintf b "%s from %a" s coproc e

and coproc b e = bprintf b "Coprocessor[%a]" exp e

and pexp b e =
  match e with
    | If _ | BinOp _ | Other _ -> par exp b e
    | _ -> exp b e

and pexp_level k b = function
  | BinOp (_, f, _) as e when level f = k ->
      let es = args e in list (sprintf " %s " f) (pexp_level (k+1)) b es
  | e -> pexp b e

and range b = function
  | Bits (n, p) -> bprintf b "[%a:%a]" num n num p
  | Flag (n, f) -> bprintf b "%s %s" n f
  | Index e -> bprintf b "[%a]" exp e;;

let rec inst k b i = indent b k; inst_sc k b i

and inst_sc k b i =
  match i with
    | Unpredictable | Affect _ | Proc _ | Misc _ | Assert _ ->
	bprintf b "%a;" (inst_aux k) i
    | _ -> bprintf b "%a" (inst_aux k) i

and inst_aux k b = function
  | Block is ->
      bprintf b "begin\n%a%aend"
	(list "" (postfix "\n" (inst k))) is indent k
  | Unpredictable -> bprintf b "UNPREDICTABLE"
  | Affect (Reg (Num "15", None), e) -> bprintf b "PC = %a" exp e
  | Affect (e1, e2) -> bprintf b "%a = %a" exp e1 exp e2
  | IfThenElse (e, i, None) ->
      bprintf b "if %a then\n%a" exp e (inst (k+4)) i
  | IfThenElse (e, i1, Some i2) ->
      bprintf b "if %a then\n%a\n%aelse %a"
	exp e (inst (k+4)) i1 indent k (inst_sc k) i2
  | Proc (f, es) -> bprintf b "%s(%a)" f (list ", " exp) es
  | While (e, i) -> bprintf b "while %a do\n%a" exp e (inst (k+4)) i
  | Assert e -> bprintf b "assert %a" exp e
  | For (s, n, p, i) ->
      bprintf b "for %s = %a to %a do\n%a" s num n num p (inst (k+4)) i
  | Misc ss -> list " " string b ss
  | Coproc (c, "send", e :: _) -> bprintf b "send %a to %a" exp e coproc c
  | Coproc (c, "load", e :: _) -> bprintf b "load %a for %a" exp e coproc c
  | Coproc (c, s, _) -> bprintf b "%a %s" coproc c s;;

let version b k = bprintf b "(%s)" k;;

let var b s = bprintf b "<%s>" s;;

let ident b i =
  bprintf b "%s%a%a" i.iname (list "" var) i.ivars
    (option " " version) i.iversion;;

let prog b p =
  bprintf b "%s %a\n%a\n" p.pref
    (list ", " ident) (p.pident :: p.paltidents) (inst 9) p.pinst;;

let lib b ps = list "" prog b ps;;
