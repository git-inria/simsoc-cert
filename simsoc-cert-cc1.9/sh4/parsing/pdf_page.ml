(**
SimSoC-Cert, a Coq library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the SH4 architecture following the:

SH-4, Software Manual, Renesas 32-Bit RISC, Rev.6.00 2006.09

Page numbers refer to Renesas_SH4_2006.pdf.


*)

module type PDF_PAGE = 
sig
  type t

  val open_in : string (** filename *) -> t
  val open_in_channel : in_channel -> t

(* val input_page : t -> (string list * t) option *)
  val input_page_rev : t -> (string list * t) option (** return the lines of the page in reverse order *)
  (** Complexity notes : Besides several calls to [input_line], for each page we call one [String.sub] *)
  val throw_page : t -> int -> t (** [throw_page _ n] read [max n 0] pages and ignores them *)

  val pos : t -> int (** current page number, first page is the number 0 *)

  val close_in : t -> unit (** remark : this function can be deleted if we prefer to close the channel after an End_of_file *)
end

module PDF_page : PDF_PAGE = 
struct
  (** The output of pdftotext contains the '\x0C' byte at the first character of some lines, indicating a new page. The last byte of the file is also '\x0C'.
      The goal of this module is to help the manipulation of such files. In particular, [input_page_rev] returns a list of lines representing a single page, without the '\x0C' mark. *)

  type t = { ic : in_channel ; next : string option ; pos : int }
  (** By concatenating [next] with [ic], we have the whole file being processing.
      The field [next] is considered as a lookahead buffer, to be able to detect the '\x0C' byte. *)

  let input_line ic = try Some (input_line ic) with End_of_file -> None

  let open_in_channel ic = 
    { ic = ic ; next = input_line ic ; pos = 0 }

  let open_in fic = 
    open_in_channel (open_in_bin fic)

  let input_page_rev t = 
    let rec aux l =
      match input_line t.ic with
        | None -> (* end of file reached *)
          if l = [""] then
            None
          else (* WARNING this pdf file does not end with '\x0C' as last byte, we can return the whole end by default *)
            assert false (* Some (l, { t with next = None ; pos = succ t.pos }) *)
        | Some s -> 
          if s <> "" && s.[0] = '\x0C' then (** In case we have a mark signaling a new page, we take the rest of the string as the new buffer *)
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
