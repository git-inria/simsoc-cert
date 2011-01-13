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

let num = string;;

let string_of_mode = function
  | Fiq -> "fiq"
  | Irq -> "irq"
  | Svc -> "svc"
  | Abt -> "abt"
  | Und -> "und"
  | Usr -> "usr"
  | Sys -> "sys";;

let mode b m = string b (string_of_mode m);;

let string_of_size = function
  | Byte -> "1"
  | Half -> "2"
  | Word -> "4";;

let size b s = string b (string_of_size s);;

let level = function
  | "and" -> 0
  | "==" | "!=" | "is" | "is_not" | ">=" | "<" -> 1
  | "+" | "-" -> 2
  | _ -> -1;;

let rec exp b = function
  | Bin s | Hex s | Num s -> string b s
  | Float_zero -> string b "0."
  | If_exp (e1, e2, e3) ->
      bprintf b "if %a then %a else %a" exp e1 exp e2 exp e3
  | BinOp (_, f, _) as e -> pexp_level (level f) b e
  | Fun (f, es) -> bprintf b "%s(%a)" f (list ", " exp) es
  | CPSR -> string b "CPSR"
  | SPSR None -> string b "SPSR"
  | SPSR (Some m) -> bprintf b "SPSR_%a" mode m
  | Reg (Num "14", None) -> string b "LR"
  | Reg (e, o) -> bprintf b "R%a%a" pexp e (option "_" mode) o
  | Var s -> string b s
  | Range (CPSR, (Flag _ as r)) -> bprintf b "%a" range r
  | Range (e, (Flag _ as r)) -> bprintf b "%a %a" pexp e range r
  | Range (e, r) -> bprintf b "%a%a" pexp e range r
  | Unpredictable_exp -> string b "UNPREDICTABLE"
  | Unaffected -> string b "unaffected"
  | Memory (e, n) -> bprintf b "Memory[%a,%a]" exp e size n
  | Coproc_exp (e, "NotFinished", _) -> bprintf b "NotFinished(%a)" coproc e
  | Coproc_exp (e, s, _) -> bprintf b "%s from %a" s coproc e

and coproc b e = bprintf b "Coprocessor[%a]" exp e

and pexp b e =
  match e with
    | If_exp _ | BinOp _ -> par exp b e
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
    | Unpredictable | Affect _ | Proc _ | Assert _ ->
	bprintf b "%a;" (inst_aux k) i
    | _ -> bprintf b "%a" (inst_aux k) i

and inst_aux k b = function
  | Block is ->
      bprintf b "begin\n%a%aend"
	(list "" (postfix "\n" (inst k))) is indent k
  | Let (n, ns, is, i) ->
      bprintf b "let %s %a =\n%abegin\n%a%aend in\n%a%a"
	n   (list " " (fun b (_, x) -> string b x)) ns   indent k
	(list "" (postfix "\n" (inst k))) is   indent k   
	indent k   (postfix "\n" (inst k)) i
  | Unpredictable -> bprintf b "UNPREDICTABLE"
  | Affect (Reg (Num "15", None), e) -> bprintf b "PC = %a" exp e
  | Affect (e1, e2) -> bprintf b "%a = %a" exp e1 exp e2
  | If (e, i, None) -> bprintf b "if %a then\n%a" exp e (inst (k+4)) i
  | If (e, i1, Some i2) ->
      bprintf b "if %a then\n%a\n%aelse %a"
	exp e (inst (k+4)) i1 indent k (inst_sc k) i2
  | Proc (f, es) -> bprintf b "%s(%a)" f (list ", " exp) es
  | While (e, i) -> bprintf b "while %a do\n%a" exp e (inst (k+4)) i
  | Assert e -> bprintf b "assert %a" exp e
  | For (s, n, p, i) ->
      bprintf b "for %s = %a to %a do\n%a" s num n num p (inst (k+4)) i
  | Coproc (c, "send", e :: _) -> bprintf b "send %a to %a" exp e coproc c
  | Coproc (c, "load", e :: _) -> bprintf b "load %a for %a" exp e coproc c
  | Coproc (c, s, _) -> bprintf b "%a %s" coproc c s
  | Case (e, nis, oi) ->
      bprintf b "case %a of\n%abegin\n%a%aend\n%adefaultcase\n%a\n%aendcase"
        exp e indent (k+4) (list "" (case_aux (k+4))) nis indent (k+4) indent (k+4) 
	(option "" (inst (k+4))) oi indent k
  | Return e -> 
      bprintf b "return %a" exp e

and case_aux k b (n, i) =
  bprintf b "%a%a\n%a\n" indent k num n (inst (k+4)) i;;

let variant b k = bprintf b "(%s)" k;;

let param b s = bprintf b "<%s>" s;;

let ident b i =
  bprintf b "%s%a%a" i.iname (list "" param) i.iparams
    (option " " variant) i.ivariant;;

let string_of_addr_mode = function
  | 1 -> "Data processing operands"
  | 2 -> "Load and Store Word or Unsigned Byte"
  | 3 -> "Miscellaneous Loads and Stores"
  | 4 -> "Load and Store Multiple"
  | 5 -> "Load and Store Coprocessor"
  | _ -> invalid_arg "Genpc.string_of_addr_mode";;

let addr_mode b m = string b (string_of_addr_mode m);;

let name b p =
  match p.pkind with
    | InstARM | InstThumb -> bprintf b "%a" (list ", " ident) (p.pident :: p.pidents)
    | Mode m ->
	bprintf b "%a - %s" addr_mode m (remove_underscores p.pident.iname);;

let block = function
  | Block _ as i -> i
  | i -> Block [i];;

let prog b p =
  bprintf b "%s %a\n%a\n" p.pref name p (inst 9) (block p.pinst);;

let lib b ps = 
  bprintf b "%a\n%a" (list "" (inst 9)) ps.header   (list "" prog) ps.body;;
