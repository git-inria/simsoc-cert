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

type index =
| IndNum of num
| IndVar of string;;

type range =
| Full
| Bit of num
| Bits of num * num
| Flag of string * string
| Index of index list

and exp =
| Num of num
| Bin of string
| Hex of string
| State of state * range
| If of exp * exp * exp
| Fun of string * exp list
| BinOp of exp * string * exp
| Other of string list

and state =
| CPSR
| SPSR of processor_exception_mode
| Reg of processor_exception_mode option * num
| Var of string;;

type inst =
| Block of inst list
| Unpredictable
| Affect of (state * range) * exp
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

let postfix p f b x = bprintf b "%a%s" f x p;;

let endline f b x = postfix "\n" f b x;;

let rec indent b i = if i > 0 then bprintf b " %a" indent (i-1);;

let string b s = bprintf b "%s" s;;

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

let state b = function
  | CPSR -> string b "CPSR"
  | SPSR m -> bprintf b "SPSR_%a" mode m
  | Reg (None, "14") -> string b "LR"
  | Reg (None, "15") -> string b "PC"
  | Reg (None, n) -> bprintf b "R%a" num n
  | Reg (Some m, n) -> bprintf b "R%a_%a" num n mode m
  | Var s -> string b s;;

let index b = function IndNum s | IndVar s -> string b s;;

let rec range b = function
  | Full -> ()
  | Bit n -> bprintf b "[%a]" num n
  | Bits (n, p) -> bprintf b "[%a:%a]" num n num p
  | Flag (n, f) -> bprintf b "%s %s" n f
  | Index is -> bprintf b "[%a]" (list "," index) is

and state_range b (s, r) =
  match s, r with
    | CPSR, Flag _ -> bprintf b "%a" range r
    | s, Full -> bprintf b "%a" state s
    | s, Flag _ -> bprintf b "%a %a" state s range r
    | s, _ -> bprintf b "%a%a" state s range r

and exp b = function
  | Bin s | Hex s | Num s -> string b s
  | State (s, r) -> state_range b (s, r)
  | If (e1, e2, e3) -> bprintf b "if %a then %a else %a" exp e1 exp e2 exp e3
  | BinOp (e1, f, e2) -> bprintf b "%a %s %a" exp e1 f exp e2
  | Fun (f, es) -> bprintf b "%s(%a)" f (list "," exp) es
  | Other ss -> list " " string b ss;;

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
  | Unpredictable -> string b "UNPREDICTABLE"
  | Affect (sr, e) -> bprintf b "%a = %a" state_range sr exp e
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
