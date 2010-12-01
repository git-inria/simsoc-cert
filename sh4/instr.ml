module type PDF_PAGE = 
sig
  type t

  val open_in : string (** filename *) -> t
  val open_in_channel : in_channel -> t
(* val input_page : t -> (string list * t) option *)
  val input_page_rev : t -> (string list * t) option (** return the lines of the page in reverse order *)
  val throw_page : t -> int -> t (** [throw_page _ n] read [max n 0] pages and ignores them *)
  val pos : t -> int (** current page number, first page is the number 0 *)
  val close_in : t -> unit (** remark : this function can be deleted if we prefer to close the channel after an End_of_file *)
end

module PDF_page : PDF_PAGE = 
struct
  type t = { ic : in_channel ; next : string option ; pos : int }

  let input_line ic = try Some (input_line ic) with End_of_file -> None

  let open_in_channel ic = 
    { ic = ic ; next = input_line ic ; pos = 0 }

  let open_in fic = 
    open_in_channel (open_in_bin fic)

  let input_page_rev t = 
    let rec aux l =
      match input_line t.ic with
	| None -> 
	  if l = [""] then
	    None
	  else
	  (* WARNING this pdf file does not end with '\x0C' as last byte, we return the whole end by default *)
	    Some (l, { t with next = None ; pos = succ t.pos })
	| Some s -> 
	  if s <> "" && s.[0] = '\x0C' then
	    Some (l, { t with next = Some (String.sub s 1 (pred (String.length s))) ; pos = succ t.pos })
	  else
	    aux (s :: l) in
    match t.next with
      | None -> None
      | Some s -> aux [s]

  let throw_page = 
    let rec aux t n = 
      if n <= 0 then
	t
      else
	match input_page_rev t with
	  | None -> t (* WARNING End_of_file reached, this function stops now by default *)
	  | Some (_, t) -> aux t (pred n) in
    aux

  let pos t = t.pos

  let close_in t = close_in t.ic
end

module type SH4_SECTION9 = 
sig
  type t

  val init9 : string (* filename *) -> t
  val init9_channel : in_channel -> t
  val input_instr : t -> (string list list * t) option
  val pos : t -> int
  val close_in : t -> unit
end

module SH4_section9 : SH4_SECTION9 = 
struct

  module P = PDF_page

  type t = { ic : P.t ; pos : int ; next : string list option }
  exception Unknown_header
  exception Unknown_footer

  let nb_page_to_ignore = 214 (* Section 9 begins at page 215 *)  + 14 (* the intro at the beginning of section 9 is not done yet... *)
  let nb_page_to_read = 202 (* the whole section 9 *)

  let del_line = 
    let rec aux = function 
      | "" :: l -> aux l
      | l -> l in
    aux 

  let input_page_fmt9 =
    let r_head, r_foot1, r_foot2 = 
      Str.regexp " *Section 9 Instruction Descriptions *", 
      Str.regexp " *REJ09B0318-0600 *", 
      Str.regexp " *Rev. 6.00 Sep 13, 2006 page [0-9]+ of 424 *" in
    let l_match = List.for_all (fun (r, x) -> Str.string_match r x 0) in
    fun t ->
    match P.input_page_rev t with
      | None -> None
      | Some (l, t) -> Some ((
	match l with
	  | x1 :: x2 :: xs when l_match [r_foot1, x1; r_foot2, x2] -> 
	    (match List.rev (del_line xs) with
	      | x :: xs when l_match [r_head, x] -> del_line xs
	      | xs -> raise Unknown_header (*; (* WARNING this unknown header is kept by default *) xs*)
	    ) 
 	  | _ -> raise Unknown_footer (*; (* WARNING this unknown footer is kept by default *) List.rev l*)
      ), t)

  let init9_ f_open f = 
    let t = P.throw_page (f_open f) nb_page_to_ignore in
    match input_page_fmt9 t with
      | None -> { ic = t ; pos = 0 ; next = None }
      | Some (l, t) -> { ic = t ; pos = 0 ; next = Some l }

  let init9 = init9_ P.open_in
  let init9_channel = init9_ P.open_in_channel

  let input_instr =
    let r = Str.regexp "9\\.[0-9]+ +" in
    fun t ->
    let rec aux ll = 
      match try Some (input_page_fmt9 t.ic) with Unknown_header -> None | Unknown_footer -> None with
	| None -> None
	| Some o -> match o with
	    | None -> 
	      if ll = [] then
		None
	      else
		Some (ll, { t with next = None ; pos = succ t.pos })
	    | Some (l, tt) ->
	      match l with 
		| x :: _ when (if Str.string_match r x 0 then true else ((*Printf.printf "%s\n%!" x;*) false)) -> Some (ll, { t with ic = tt ; next = Some l ; pos = succ t.pos })
		| _ -> aux (l :: ll) in
    match t.next with
      | None -> None
      | Some l -> aux [l]

  let pos t = t.pos

  let close_in t = P.close_in t.ic
end

let _ = 
  let module S = SH4_section9 in

  let t = S.init9_channel stdin in

  let split_at f = 
    let rec aux l_pred = function
	| x :: xs -> 
	  if f x then
	    Some (List.rev l_pred, x, xs)
	  else
	    aux (x :: l_pred) xs
	| [] -> None in
    aux [] in

  let split_err s l = match split_at s l with None -> assert false | Some s -> s in

  let rec aux t =
    match S.input_instr t with 
      | None -> ()
      | Some (l, t) -> 
	let l = List.flatten (List.rev l) in
	let l1, _, l = split_err ((=) "Description") l in
	let l2, _, l = split_err ((=) "Operation") l in
	let l3, n, l = 
	  try split_err (fun x -> x <> "" && List.for_all (fun c -> x.[0] <> c) [' ' ; '{' ; '}'] ) l 
	  with _ -> "ZZZZZZZZZZZZZZZZZZZZZZZ" :: l, "", [] in
	begin
	  List.iter (fun s -> Printf.printf "%s\n" s) l1; 
	  Printf.printf "DDDDDDDDDDDDDDDDDDDDDDD \n%!" ;
	  List.iter (fun s -> Printf.printf "%s\n" s) l2; 
	  Printf.printf "OOOOOOOOOOOOOOOOOOOOOOO \n%!" ;
	  List.iter (fun s -> Printf.printf "%s\n" s) l3; 
	  Printf.printf "EEEEEEEEEEEEEEEEEEEEEEE \n%s\n%!" n;
	  List.iter (fun s -> Printf.printf "%s\n" s) l; 
	  Printf.printf "_______________________ %d\n%!" (S.pos t);
	  aux t;
	end in
  begin
    aux t;
  end

