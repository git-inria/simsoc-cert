(**
SimSoC-Cert, a library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Pseudocode abstract syntax tree.
*)

(****************************************************************************)
(** Pseudo-code expressions and instructions *)
(****************************************************************************)

type processor_exception_mode = Fiq | Irq | Svc | Abt | Und;;

type num = string;;

type exp =
| Num of num
| Bin of string
| Hex of string
| If of exp * exp * exp
| Fun of string * exp list
| BinOp of exp * string * exp
| Other of string list
| CPSR
| SPSR of processor_exception_mode
| Reg of (num * processor_exception_mode option)
| Var of string
| RdPlus1
| Range of exp * range
| Unaffected
| UnpredictableValue

and range =
| Bits of num * num
| Flag of string * string
| Index of exp list;;

type inst =
| Block of inst list
| Unpredictable
| Affect of exp * exp
| IfThenElse of exp * inst * inst option
| Proc of string * exp list
| While of exp * inst
| Assert of exp
| For of string * num * num * inst
| Misc of string list;;

type prog = string * string * num option * inst;;

(****************************************************************************)
(** Printing functions *)
(****************************************************************************)

open Printf;;

let string b s = bprintf b "%s" s;;

let postfix p f b x = bprintf b "%a%s" f x p;;

let endline f b x = postfix "\n" f b x;;

let rec indent b i = if i > 0 then bprintf b " %a" indent (i-1);;

let list_iter f b xs = List.iter (f b) xs;;

let list sep f =
  let rec aux b = function
    | [] -> ()
    | [x] -> f b x
    | x :: xs -> bprintf b "%a%s%a" f x sep aux xs
  in aux;;

let option f b = function
  | None -> ()
  | Some x -> f b x;;

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
  | If (e1, e2, e3) -> bprintf b "if %a then %a else %a" exp e1 exp e2 exp e3
  | BinOp (e1, f, e2) -> bprintf b "%a %s %a" exp e1 f exp e2
  | Fun (f, es) -> bprintf b "%s(%a)" f (list "," exp) es
  | Other ss -> list " " string b ss
  | CPSR -> string b "CPSR"
  | SPSR m -> bprintf b "SPSR_%a" mode m
  | Reg ("14", None) -> string b "LR"
  | Reg ("15", None) -> string b "PC"
  | Reg (n, None) -> bprintf b "R%a" num n
  | Reg (n, Some m) -> bprintf b "R%a_%a" num n mode m
  | Var s -> string b s
  | RdPlus1 -> string b "R(d+1)"
  | Range (CPSR, (Flag _ as r)) -> bprintf b "%a" range r
  | Range (BinOp _ as e, r) -> bprintf b "(%a)%a" exp e range r
  | Range (e, (Flag _ as r)) -> bprintf b "%a %a" exp e range r
  | Range (e, r) -> bprintf b "%a%a" exp e range r
  | UnpredictableValue -> string b "Unpredictable"
  | Unaffected -> string b "Unaffected"

and range b = function
  | Bits (n, p) -> bprintf b "[%a:%a]" num n num p
  | Flag (n, f) -> bprintf b "%s %s" n f
  | Index es -> bprintf b "[%a]" (list "," exp) es;;

let rec inst k b i = indent b k;
  match i with
    | Block _ | IfThenElse (_, Block _, None)
    | IfThenElse (_, _, Some (Block _|IfThenElse _)) ->
	bprintf b "%a" (inst_aux k) i
    | Unpredictable | Affect _ | IfThenElse _ | Proc _ | Misc _ | While _
    | Assert _ | For _  ->
	bprintf b "%a;" (inst_aux k) i

and inst_aux k b = function
  | Block is ->
      bprintf b "begin\n%a%aend"
	(list "" (postfix "\n" (inst k))) is indent k
  | Unpredictable -> bprintf b "UNPREDICTABLE"
  | Affect (e1, e2) -> bprintf b "%a = %a" exp e1 exp e2
  | IfThenElse (e, i, None) ->
      bprintf b "if %a then\n%a" exp e (inst (k+4)) i
  | IfThenElse (e, i1, Some i2) ->
      bprintf b "if %a then\n%a\n%aelse %a"
	exp e (inst (k+4)) i1 indent k (inst_aux k) i2
  | Proc (f, es) -> bprintf b "%s(%a)" f (list "," exp) es
  | While (e, i) -> bprintf b "while %a do %a" exp e (inst (k+4)) i
  | Assert e -> bprintf b "assert %a" exp e
  | For (s, n, p, i) ->
      bprintf b "for %s = %a to %a do %a" s num n num p (inst (k+4)) i
  | Misc ss -> list " " string b ss;;

let version b k = bprintf b " (%s)" k;;

let prog b (r, f, v, i) =
  bprintf b "%s %s%a;\n%a\n" r f (option version) v (inst 9) i;;
