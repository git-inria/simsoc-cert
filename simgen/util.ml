(**
SimSoC-Cert, a toolkit for generating certified processor simulators
See the COPYRIGHTS and LICENSE files.

Functions of general interest about lists, printing, etc.
*)

open Printf;;

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
   Intuitively, we can easily retrieve [l] from the partition, by applying a
   [List.flatten] to it (modulo a call to [List.map snd]). *)
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
let array_map2 =
  let get = Array.unsafe_get in
    fun f a b ->
      let l = Array.length a in
        assert (l = Array.length b);
        if l = 0 then [||] else begin
          let r = Array.create l (f (get a 0) (get b 0)) in
            for i = 1 to l - 1 do
              Array.set r i (f (get a i) (get b i))
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

module Str = 
struct 
  include Str

  let l_match = List.for_all (fun (r, x) -> Str.string_match r x 0)

  let str_match r s l = 
    if Str.string_match (Str.regexp r) s 0 then
      Some (List.map (fun i -> Str.matched_group i s) l)
    else 
      None
end

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

let list_sep sep f =
  let rec aux b = function
    | [] -> ()
    | [x] -> f b x
    | x :: xs -> bprintf b "%a%s%a" f x sep aux xs
  in aux;;

let list f = list_sep "" f;;

let option p f b = function
  | None -> ()
  | Some x -> prefix p f b x;;

let pair f sep g b (x,y) = bprintf b "%a%s%a" f x sep g y;;
let first f b (x,_) = f b x;;
let second f b (_,x) = f b x;;

let par f b x = bprintf b "(%a)" f x;;

let rec indent b i = if i > 0 then bprintf b " %a" indent (i-1);;

let berr = Buffer.create 10000;;

at_exit (fun () -> Buffer.output_buffer stderr berr);;

let print f x =
  let b = Buffer.create 10000 in f b x; Buffer.output_buffer stdout b;;

(*****************************************************************************)
(** transitive closure of a graph (code taken from CoLoR) *)
(*****************************************************************************)

module TransClos (X : Set.OrderedType) = struct

  module XSet = Set.Make (X);;
  module XMap = Map.Make (X);;

  type graph = XSet.t XMap.t;;

  let empty = XMap.empty;;

  let succs x g = try XMap.find x g with Not_found -> XSet.empty;;

  let mem x y g = XSet.mem y (succs x g);;

  let add_edge x y g = XMap.add x (XSet.add y (succs x g)) g;;

  let add_pred x s w sw g =
      if XSet.mem x sw then XSet.fold (add_edge w) s g else g;;

  let trans_add_edge x y g =
    (* if (x,y) is already in g, do nothing *)
    if XSet.mem y (succs x g) then g
      (* otherwise, for every pair (w,x) in g,
         add a pair (w,z) for every z in {y} U (succs y g) *)
    else let ysy = XSet.add y (succs y g) in
      XMap.fold (add_pred x ysy) g
        (* and, for every z in {y} U (succs y g), add a pair (x,z) *)
        (XSet.fold (add_edge x) ysy g);;

  let bindings g =
    XMap.fold (fun x s l -> XSet.fold (fun y l -> (x,y)::l) s l) g [];;

  let nodes g =
    XMap.fold (fun x s l -> XSet.fold (fun y l -> y::l) s (x::l)) g [];;

  let rec level x g =
    let s = succs x g in
      if s = XSet.empty then 0
      else 1 + XSet.fold (fun y m -> max (level y g) m) s 0;;

  let level_map g =
    List.fold_left (fun m x -> XMap.add x (level x g) m) XMap.empty (nodes g);;

  let set elt b = XSet.iter (bprintf b "%a," elt);;

  let graph elt b =
    XMap.iter (fun x s -> bprintf b "succs(%a)={%a}\n" elt x (set elt) s);;

end;;
