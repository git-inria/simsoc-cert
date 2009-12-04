(**
SimSoC-Cert, a library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Pseudocode abstract syntax tree.
*)

(****************************************************************************)
(** Pseudo-code expressions *)
(****************************************************************************)

type num = int;; (*IMPROVE: use a private data type?*)

type word = int;; (*FIXME: use int32?*)

let word_of_num n = n;;

type processor_exception_mode = Fiq | Irq | Svc | Abt | Und;;

type flag = N | Z | C | V;;

type range = Bit of num | Bits of num * num;;

type exp =
| Word of word
| State of sexp
| If of exp * exp * exp
| Fun of string * exp list
| Range of exp * range
| Other of string list

and sexp =
| CPSR
| SPSR of processor_exception_mode
| Reg of processor_exception_mode option * num
| Var of string
| Flag of flag;;

(****************************************************************************)
(** Pseudo-code instructions *)
(****************************************************************************)

type inst =
| Block of inst list
| Unpredictable
| Affect of sexp * range option * exp
| IfThenElse of exp * inst * inst option;;

type prog = string * string * inst;;

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

let string_of_flag = function
  | N -> "N"
  | Z -> "Z"
  | C -> "C"
  | V -> "V";;

let flag b f = string b (string_of_flag f);;

let num b n = bprintf b "%d" n;;
let word b w = bprintf b "%d" w;;

let range b = function
  | Bit n -> bprintf b "%a" num n
  | Bits (n, p) -> bprintf b "%a:%a" num n num p;;

let sexp b = function
  | CPSR -> string b "CPSR"
  | SPSR m -> bprintf b "SPSR_%a" mode m
  | Reg (None, n) -> bprintf b "R%a" num n
  | Reg (Some m, n) -> bprintf b "R%a_%a" num n mode m
  | Var s -> string b s
  | Flag f -> bprintf b "%a Flag" flag f;;

let rec exp b = function
  | Word w -> word b w
  | State se -> sexp b se
  | If (e1, e2, e3) -> bprintf b "if %a then %a else %a" exp e1 exp e2 exp e3
  | Fun (f, es) -> bprintf b "%s(%a)" f (list "," exp) es
  | Range (e, r) -> bprintf b "%a[%a]" exp e range r
  | Other ss -> list " " string b ss;;

let rec inst k b i =
  match i with
    | Block _ | IfThenElse (_, Block _, _) ->
	bprintf b "%a%a" indent k (inst_aux k) i
    | Unpredictable | Affect _ | IfThenElse _ ->
	bprintf b "%a%a;" indent k (inst_aux k) i

and inst_aux k b = function
  | Block is ->
      bprintf b "begin\n%a%aend"
	(list "" (postfix "\n" (inst k))) is indent k
  | Unpredictable ->
      string b "UNPREDICTABLE"
  | Affect (se, ro, e) ->
      bprintf b "%a%a = %a" sexp se (option range) ro exp e
  | IfThenElse (e, i, None) ->
      bprintf b "if %a then\n%a" exp e (inst (k+4)) i
  | IfThenElse (e, i1, Some i2) ->
      bprintf b "if %a then\n%a\n%aelse %a"
	exp e (inst (k+4)) i1 indent k (inst_aux k) i2;;

let prog b (r, f, i) = bprintf b "%s %s;\n%a" r f (inst 9) i;;
