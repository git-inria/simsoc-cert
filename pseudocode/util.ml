(**
SimSoC-Cert, a library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Functions of general interest about lists, printing, etc.
*)

open Printf;;

(*****************************************************************************)
(** functions on lists *)
(*****************************************************************************)

(* (firsts f l) returns the pair (l1,l2) such that l1 is the prefix of
   l satisfying f and l2 is the remaining part of l *)
let firsts f =
  let rec aux acc = function
    | [] -> List.rev acc, []
    | x :: xs as l -> if f x then aux (x :: acc) xs else List.rev acc, l
  in aux [];;

(*****************************************************************************)
(** functions on strings *)
(*****************************************************************************)

(* return a copy of s where underscores are replaced by spaces *)
let remove_underscores s =
  let s = String.copy s in
    for i = 0 to String.length s - 1 do
      if s.[i] = '_' then s.[i] <- ' '
    done; s;;

module StrOrd = struct
  type t = string
  let compare = Pervasives.compare
end;;

module StrSet = Set.Make (StrOrd);;
module StrMap = Map.Make (StrOrd);;

let set_of_list =
  List.fold_left (fun set s -> StrSet.add s set) StrSet.empty;;

let list_of_map m =
  List.sort (fun (s1,_) (s2,_) -> Pervasives.compare s1 s2)
    (StrMap.fold (fun s t l -> (s,t)::l) m []);;

(*****************************************************************************)
(** combinators for printing in a buffer *)
(*****************************************************************************)

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

let print f x =
  let b = Buffer.create 10000 in f b x; Buffer.output_buffer stdout b;;

(*****************************************************************************)
(** warnings or errors *)
(*****************************************************************************)

let warning s = fprintf stderr "warning: %s\n" s;;

let error s = fprintf stderr "error: %s\n" s; exit 1;;

(*****************************************************************************)
(** generic functions for handling references *)
(*****************************************************************************)

let get_set init =
  let r = ref init in
    (fun () -> !r),
    (fun v -> r := v);;

let get_set_bool() =
  let r = ref false in
    (fun () -> !r),
    (fun () -> r := true);;

let is_set_get_set m init =
  let r = ref init and s = ref false in
    (fun () -> !s),
    (fun () -> if !s then !r else error (sprintf "no %s provided" m)),
    (fun v -> if !s then error (sprintf "%s already provided" m)
              else (r := v; s := true));;

(*****************************************************************************)
(** verbose and debug modes *)
(*****************************************************************************)

let get_verbose, set_verbose = get_set_bool();;
let get_debug, set_debug = get_set_bool();;

let fverbose fmt f x = if get_verbose() then fprintf stderr fmt f x else ();;

let verbose x = if get_verbose() then fprintf stderr "%s" x else ();;
