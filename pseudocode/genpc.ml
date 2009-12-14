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

let rec exp b = function
  | Bin s | Hex s | Num s -> string b s
  | If (e1, e2, e3) -> bprintf b "if %a then %a else %a" pexp1 e1 exp e2 exp e3
  | BinOp ((Other _ as e1), ("+"|"or" as f), e2) ->
      bprintf b "%a %s %a" exp e1 f pexp1 e2
  | BinOp (e, ("+"|"*"|"-"|"<<" as f), Num n) when e <> Var "address" ->
      bprintf b "%a%s%s" exp e f n
  | BinOp (e1, f, e2) -> bprintf b "%a %s %a" pexp1 e1 f pexp1 e2
  | Fun (("NOT" as f), [e]) -> bprintf b "%s %a" f pexp e
  | Fun (("is_even_numbered" as f), [e]) -> bprintf b "%a %s" exp e f
  | Fun (f, es) -> bprintf b "%s(%a)" f (list ", " exp) es
  | Other ss -> list " " string b ss
  | CPSR -> string b "CPSR"
  | SPSR None -> string b "SPSR"
  | SPSR (Some m) -> bprintf b "SPSR_%a" mode m
  | Reg ("14", None) -> string b "LR"
  | Reg (n, None) -> bprintf b "R%a" num n
  | Reg (n, Some m) -> bprintf b "R%a_%a" num n mode m
  | Var s -> string b s
  | RdPlus1 -> string b "R(d+1)"
  | Range (CPSR, (Flag _ as r)) -> bprintf b "%a" range r
  | Range (e, (Flag _ as r)) -> bprintf b "%a %a" pexp e range r
  | Range (e, r) -> bprintf b "%a%a" pexp e range r
  | UnpredictableValue -> string b "UNPREDICTABLE"
  | Unaffected -> string b "unaffected"

(* put parentheses around complex expressions *)
and pexp b e =
  match e with
    | If _ | BinOp _ | Other _ | Range (_, Flag _) -> par exp b e
    | _ -> exp b e

(* put parentheses around complex expressions,
except some binary operations *)
and pexp1 b e =
  match e with
    | BinOp (_, f, _) when f <> "Rotate_Right" && f <> "or" && f <> "*"
	&& f <> "<<" -> exp b e
    | Range (_, Flag _) -> exp b e
    | _ -> pexp b e

and range b = function
  | Bits (n, p) -> bprintf b "[%a:%a]" num n num p
  | Flag (n, f) -> bprintf b "%s %s" n f
  | Index [e; Num n] -> bprintf b "[%a,%s]" exp e n
  | Index es -> bprintf b "[%a]" (list ", " exp) es;;

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
  | Affect (Reg ("15", None), e) -> bprintf b "PC = %a" exp e
  | Affect (e1, e2) -> bprintf b "%a = %a" exp e1 exp e2
  | IfThenElse (e, i, None) ->
      bprintf b "if %a then\n%a" pexp1 e (inst (k+4)) i
  | IfThenElse (e, i1, Some i2) ->
      bprintf b "if %a then\n%a\n%aelse %a"
	pexp1 e (inst (k+4)) i1 indent k (inst_sc k) i2
  | Proc (f, es) -> bprintf b "%s(%a)" f (list ", " exp) es
  | While (e, i) -> bprintf b "while %a do\n%a" exp e (inst (k+4)) i
  | Assert e -> bprintf b "assert %a" exp e
  | For (s, n, p, i) ->
      bprintf b "for %s = %a to %a do\n%a" s num n num p (inst (k+4)) i
  | Misc ss -> list " " string b ss;;

let version b k = bprintf b " (%s)" k;;

let var b s = bprintf b "<%s>" s;;

let prog b p =
  bprintf b "%s %a%a%a\n%a\n" p.pref
    (list ", " string) (p.pname :: p.paltnames) (list "" var) p.pvars
    (option version) p.pversion (inst 9) p.pinst;;

let lib b ps = list "" prog b ps;;
