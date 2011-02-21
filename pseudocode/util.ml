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

(* Similar to Array.iteri *)
let list_iteri f l =
  let rec aux n f = function
    | hd :: tl -> f n hd; aux (n+1) f tl
    | [] -> ()
  in aux 0 f l;;

(* [separate f l] produces a partition of [l], determined by the [f] function.
 * Intuitively, we can easily retrieve [l] from the partition, by applying a
 * [List.flatten] to it (modulo a call to [List.map snd]). *)
let separate tag = 
  let cons b1 l = b1, List.rev l in
  function
    | [] -> []
    | x :: xs -> 
      let b1, l, ls =
        List.fold_left (fun (b1, l, acc) x ->
          let b2 = tag x in
          if b1 = b2 then
            b2, x :: l, acc
          else
            b2, [x], cons b1 l :: acc
        ) (tag x, [x], []) xs in
      List.rev (cons b1 l :: ls)

(*****************************************************************************)
(** functions on arrays *)
(*****************************************************************************)

(* Like List.map2, but for arrays *)
(* Code based on the OCaml implementation of Array.map *)
let array_map2 f a b =
  let l = Array.length a in
    assert (l = Array.length b);
    if l = 0 then [||] else
      begin
        let r = Array.create l (f (Array.unsafe_get a 0) (Array.unsafe_get b 0)) in
          for i = 1 to l - 1 do
            Array.unsafe_set r i (f (Array.unsafe_get a i) (Array.unsafe_get b i))
          done;
          r
      end;;

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

module Map = 
struct
  module type S = 
  sig
    include Map.S

    val add_no_erase : key -> 'a -> 'a t -> 'a t
      (* like [add] but does nothing if the [key] is already present *)
  end

  module Make (O : Map.OrderedType) : S with type key = O.t =
  struct
    module M = Map.Make (O)

    let add_no_erase k v map = if M.mem k map then map else M.add k v map
    include M
  end
end


module StrSet = Set.Make (StrOrd);;
module StrMap = Map.Make (StrOrd);;

let set_of_list =
  List.fold_left (fun set s -> StrSet.add s set) StrSet.empty;;

let list_of_map m =
  List.sort (fun (s1,_) (s2,_) -> Pervasives.compare s1 s2)
    (StrMap.fold (fun s t l -> (s,t)::l) m []);;


(*****************************************************************************)
(** functions on options *)
(*****************************************************************************)

let option_map f = function
  | None -> None
  | Some o -> Some (f o)

let option_exists f = function
  | None -> false
  | Some o -> f o

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

let begins_with b s = 
  let lg = String.length s in
  Buffer.length b >= lg && Buffer.sub b 0 lg = s

(*****************************************************************************)
(** warnings or errors *)
(*****************************************************************************)

let warning s = eprintf "warning: %s\n" s;;

let error s = eprintf "error: %s\n" s; exit 1;;

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

let fverbose fmt f x = if get_verbose() then eprintf fmt f x else ();;

let verbose x = if get_verbose() then eprintf "%s" x else ();;
