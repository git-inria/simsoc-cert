(**
SimSoC-Cert, a Coq library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the SH4 architecture following the:

SH-4, Software Manual, Renesas 32-Bit RISC, Rev.6.00 2006.09

Page numbers refer to Renesas_SH4_2006.pdf.


*)

module List = 
struct 
  include List 
    
  (** Suppress the first block of empty string (eventually) figuring at the beginning of the list *)
  let del_line = 
    let rec aux = function 
      | "" :: l -> aux l
      | l -> l in
    aux 

  (** [split_from_beg_at f l] returns [l1, x, l2] where the following conditions hold :
    - [l] is equal to [l1 @ [x] @ l2]
    - [x] is the first element in [l] such as [f x] evaluates to [true] *)
  let split_from_beg_at f =
    let rec aux l_pred = function
      | x :: xs -> 
	if f x then
          Some (List.rev l_pred, x, xs)
	else
          aux (x :: l_pred) xs
      | [] -> None in
    aux []

  (** Same as [split_from_beg_at] but the search starts at the end of the list *)
  let split_from_end_at f = 
    let rec aux l_succ = function
      | x :: xs -> 
	if f x then
          Some (List.rev xs, x, l_succ)
	else
          aux (x :: l_succ) xs
      | [] -> None in
    fun l -> aux [] (List.rev l)

  let split_beg s l = match split_from_beg_at s l with None -> assert false | Some s -> s
  let split_end s l = match split_from_end_at s l with None -> assert false | Some s -> s

  let init f =
    let rec aux l n = 
      if n = 0 then
        l
      else
        let n = pred n in
        aux (f n :: l) n in
    aux [] 
end


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
