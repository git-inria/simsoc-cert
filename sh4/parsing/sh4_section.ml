(**
SimSoC-Cert, a Coq library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the SH4 architecture following the:

SH-4, Software Manual, Renesas 32-Bit RISC, Rev.6.00 2006.09

Page numbers refer to Renesas_SH4_2006.pdf.


*)

open Pervasive
open Pdf_page

let importation_error = "We encounter an unknown string to import from the manual. It means that the manual of SH4 you give in input is different from the usual one we take, because until now it has been tested succesfully without failures."

type unknown_header = string (* this part has an unknown format *) * string list (* this part has not been analyzed *)
type ('a, 'b) page_read = 
  | Next of 'a (* string list *)
  | Last of 'b (* unknown_header *)


module type SH4_SECTION = 
sig
  type t

  val init : string (** filename *) -> t
  val init_channel : in_channel -> t

  val input_instr : t -> (string list list * t, string list * (string * string * bool) list) page_read
    (** Each call to [input_instr _] gives us a section (unit of instruction described in several pages) of the chapter 9 *)
    (** [Last _] is returned when a page doesn't match a predefined header and footer template. *)

  val c_code : t -> string list (** The small C code published at the beginning of the 9 section. *)
    (** Note that this function is pure as the importation is done only once : during [init] or [init_channel] *)
  val pos : t -> int (** The first number given by [pos] is 0. In fact, it indicates the number of time we have called [input_instr]. *)

  val close_in : t -> unit
end

module SH4_section : SH4_SECTION = 
struct
  (** This module imports the information needed in the manual. 
      During initialization (with [init] or [init_channel]), we jump directly to section 9. Then, we also import the small header written in C code at the beginning of the section 9. It describes some definitions and functions commonly used inside the pseudo-code (like declarations of variable PC, SR, R ... ).
      At the end, we import the addressing mode informations in the appendix.
  *)
  (** Remark : The algorithm of importation looks like the module [PDF_page].
   ** Instead of 
   **     - read [string]      one by one and search at the beginning a byte   '\x0C'    <- it is the end of a page
   ** we
   **     - read [string list] one by one and search at the beginning a string "9.[0-9]" <- it is the end of an instruction *)
 
  module P = PDF_page

  type t = { ic : P.t ; pos : int ; next : (string list, unknown_header) page_read ; c_code : string list }
  (** 
      - The field [next] represents the lookahead buffer, to detect the end of a section.
      - [c_code] is the "copy paste" of the code present at the beginning of the 9 section, some human explanations are however not kept. *)

  exception Unknown_header of unknown_header * P.t
  exception Unknown_footer of string list * P.t

  let nb_page_to_ignore = 214 (* Section 9 begins at page 215 *) + 1 (* we don't import the first page *) 
  let nb_page_to_read = 202 (* the whole section 9 *)


  (** Behaves like [PDF_page.input_page_rev] but the header and the footer are suppressed (along with empty lines). 
      Note that unlike [PDF_page.input_page_rev], the returned list is in natural order.
      In the case we try to input a page whose header or footer does not match the regexp, [Unknown_header _] or [Unknown_footer _] is thrown depending the case. *)
  let input_page_fmt =
    let r_foot1, r_foot2 =
      Str.regexp " *REJ09B0318-0600 *", 
      Str.regexp " *Rev. 6.00 Sep 13, 2006 page [0-9]+ of 424 *" in
    fun r_head t ->
    match P.input_page_rev t with
      | None -> None
      | Some (l, t) -> Some ((
        match l with
          | x1 :: x2 :: xs when Str.l_match [r_foot1, x1; r_foot2, x2] -> 
            (match List.rev (List.del_line xs) with
              | x :: xs ->
                if Str.l_match [r_head, x] then 
                  List.del_line xs
                else
                  raise (Unknown_header ((x, xs), t))
              | [] -> failwith importation_error
            )
          | _ -> raise (Unknown_footer (l, t))
      ), t)

  let input_page_fmt_9 = input_page_fmt (Str.regexp " *Section 9 Instruction Descriptions *")
  let input_page_fmt_a = input_page_fmt (Str.regexp " *Appendix A Instruction Codes *")

  (** Same as [input_page_fmt_9] but an error is thrown instead of returning [None] *)
  let input_page_9 t = 
    match input_page_fmt_9 t with
      | None -> assert false (* We suppose we never reach the end of file. Remark that [input_page_9] is not called directly outside the module. *) 
      | Some r -> r

  (** Same as [input_page_fmt_a] but an error is thrown instead of returning [None] *)
  let input_page_a t = 
    match input_page_fmt_a t with
      | None -> assert false (* We suppose we never reach the end of file. Remark that [input_page_a] is not called directly outside the module. *) 
      | Some r -> r

  (** [input_page_groups n _] applies [n] times [input_page_9] and returns the whole as a list (ordering is natural : the first element is the first read). *)
  let input_page_groups = 
    let rec aux ll n t = 
      if n = 0 then
        List.rev ll, t
      else
        let l, t = input_page_9 t in
        aux (l :: ll) (pred n) t in
    aux []
        
  (** We describe above the lines written in human language we don't want to keep *)
  (** Remark that the program had been run (and tested) with increasing list and valid position only *)
  let comment_c_code1 = [27; 28; 34; 35; 39; 50; 62]
  let comment_c_code2 = [1; 5; 8]

  (** [dont_keep l_num l] returns [l] but all the element figuring at position specified by [l_num] are discarded.
      We suppose [l_num] is sorted in increasing order, the first element is 0. *)
  let dont_keep = 
    let rec aux p = function 
      | n :: ns, _ :: xs when p = n -> aux (succ p) (ns, xs)
      | n :: ns, x :: xs when p < n -> x :: aux (succ p) (n :: ns, xs)
      | [], l -> l
      | _ -> assert false in
    fun l_num l ->
    aux 0 (l_num, l)

  (** Here comes the initialization of the processing, [f_open] and [f] are used to return an input channel. *)
  let init_ f_open f = 
    let t = P.throw_page (f_open f) nb_page_to_ignore in (** go to section 9 and ignore the first page of section 9 *)
    let l1, t = input_page_9 t in 
    let l2, t = input_page_9 t in 
    let ll, t = input_page_groups 10 t in (** page [3-12]  C code *)
    let t = P.throw_page t 1 in (** go to beginning of instruction *)

    let l, t = input_page_9 t in (** we read one more page for the initialization of the buffer *)
    { ic = t ; pos = 0 ; next = Next l ; c_code = List.flatten (l1 :: l2 :: ll) }

  let init = init_ P.open_in
  let init_channel = init_ P.open_in_channel

  (** The algorithm of [input_instr] is simple : we call [input_page_9] as long as we don't have a new section, characterized by the presence of the mark "9.1", "9.2", ..., "9.103" at the beginning of the new page.
      In the case we encounter the exception [Unknown_header _] or [Unknown_footer _], we just halt. 
      This solution found to detect the end of section 9 is enough, because each pages in section 9 contains the same header and footer.*)
  let input_instr =
    let r = Str.regexp "9\\.[0-9]+ +" in (** Indicates the beginning of an instruction section. (see chapter 9.) *)
    let some ll t = Next (ll, { t with pos = succ t.pos }) in
    fun t ->
      let rec aux ll = 
        match 
          try let l, tt = input_page_9 t.ic in Next l, tt with 
            | Unknown_header (x_xs, tt) -> Last x_xs, tt
        with
          | Last x_xs, tt -> some ll { t with ic = tt ; next = Last x_xs }
          | Next l, tt ->
            match l with 
              | x :: _ when Str.string_match r x 0 -> some ll { t with ic = tt ; next = Next l }
              | _ -> aux (l :: ll) in
      match t.next with
        | Next l -> aux [l]
        | Last _ -> 
          Last (
            let rec aux ll ic = 
              match 
                try Some (input_page_a ic) with 
                  | Unknown_header _ -> None
              with
                | None -> List.rev ll, ic
                | Some (l, ic) -> aux (l :: ll) ic in

            match aux [] t.ic with
              | [], _ -> failwith importation_error 
              |  l :: ls, ic -> 

                let reg_big = Str.regexp "([0-9]+) .+" in
                let reg_table = Str.regexp "Table A.[0-9]+ .+" in
                
                let separate f_reg = 
                  let rec aux acc n1 l1 = 
                    match List.split_from_beg_at f_reg l1 with
                      | None -> List.rev ((n1, List.del_line l1) :: acc)
                      | Some (l1, n2, l2) -> aux ((n1, List.del_line l1) :: acc) n2 l2 in
                  aux [] in

                let _, n1, l = List.split_beg ((=) "(1) No Operand") l in 
                let l = separate (fun s -> Str.string_match reg_big s 0) n1 (List.flatten (l :: ls)) in
                let ll = 
                  let map f = 
                    List.map (function 
                      | title, x :: xs -> title, f x xs
                      | _ -> failwith importation_error) in
                  map (fun x xs -> 
                    map (separate (fun x -> 
                      Str.string_match (Str.regexp ".+T Bit") x 0 
                      || Str.string_match (Str.regexp_string "tion") x 0
                      || Str.string_match (Str.regexp_string "on") x 0))
                      (separate (fun s -> Str.string_match reg_table s 0) x xs)
                  ) l in

                  match ll with
                    | (_, (_, (_, l1) :: l2) :: l3) :: l4 -> 
                      List.fold_left (fun l s -> 
                        if s.[0] = ' ' then 
                          l
                        else
                          let ll = Str.split (Str.regexp " +") s in
                          List.hd ll :: l) [] l1,
                          let fold_left f a l = List.fold_left (fun a (_, l) -> f a l) a l in
                          fold_left (fold_left (fold_left (List.fold_left (fun acc s -> 
                            if s = "" || s.[0] = ' ' then 
                              acc 
                            else 
                              match Str.split (Str.regexp " +") s with
                                | x1 :: x2 :: l -> 
                                  (x1, x2, List.exists ((=) "Privileged") l) :: acc
                                | _ -> failwith importation_error
                          )))) 
                            []
                            (("", ("", l2) :: l3) :: l4)
                    | _ -> failwith importation_error
          )

  let pos t = t.pos
  let c_code t = t.c_code
    
  let close_in t = P.close_in t.ic
end
