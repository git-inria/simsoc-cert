(**
SimSoC-Cert, a library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Functions of general interest about lists, printing, etc.
*)

open Printf;;

(***********************************************************************)
(** strings *)
(***********************************************************************)

module StrOrd = struct
  type t = string
  let compare = Pervasives.compare
end;;

module StrSet = Set.Make (StrOrd);;
module StrMap = Map.Make (StrOrd);;

(***********************************************************************)
(** printing in a buffer *)
(***********************************************************************)

let int b n = bprintf b "%d" n;;

let int32 b n = bprintf b "%ld" n;;

let string b s = bprintf b "%s" s;;

let prefix p f b x = bprintf b "%s%a" p f x;;

let postfix p f b x = bprintf b "%a%s" f x p;;

let endline f b x = postfix "\n" f b x;;

let list_iter f b xs = List.iter (f b) xs;;

let list sep f =
  let rec aux b = function
    | [] -> ()
    | [x] -> f b x
    | x :: xs -> bprintf b "%a%s%a" f x sep aux xs
  in aux;;

let option p f b = function
  | None -> ()
  | Some x -> prefix p f b x;;

let par f b x = bprintf b "(%a)" f x;;

let rec indent b i = if i > 0 then bprintf b " %a" indent (i-1);;
