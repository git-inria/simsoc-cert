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

(** Suppress the first block of empty string (eventually) figuring at the beginning of the list *)
let del_line = 
  let rec aux = function 
    | "" :: l -> aux l
    | l -> l in
  aux 

let l_match = List.for_all (fun (r, x) -> Str.string_match r x 0)

let importation_error = "We encounter an unknown string to import from the manual. It means that the manual of SH4 you give in input is different from the usual one we take, because until now it has been tested succesfully without failures."

type unknown_header = string (* this part has an unknown format *) * string list (* this part has not been analyzed *)
type ('a, 'b) page_read = 
  | Next of 'a (* string list *)
  | Last of 'b (* unknown_header *)


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
          | x1 :: x2 :: xs when l_match [r_foot1, x1; r_foot2, x2] -> 
            (match List.rev (del_line xs) with
              | x :: xs ->
                if l_match [r_head, x] then 
                  del_line xs
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
    let l1, t = input_page_9 t in let l1 = dont_keep comment_c_code1 l1 in (** page [1]  C code *)
    let l2, t = input_page_9 t in let l2 = dont_keep comment_c_code2 l2 in (** page [2]  C code *)
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
let l, ic = aux [] t.ic in

match l with
  | [] -> failwith importation_error 
  |  l :: ls -> 

  let reg_big = Str.regexp "([0-9]+) .+" in
  let reg_table = Str.regexp "Table A.[0-9]+ .+" in

  let separate f_reg = 
    let rec aux acc n1 l1 = 
      match split_from_beg_at f_reg l1 with
        | None -> List.rev ((n1, del_line l1) :: acc)
        | Some (l1, n2, l2) -> aux ((n1, del_line l1) :: acc) n2 l2 in
    aux [] in

  let _, n1, l = split_beg ((=) "(1) No Operand") l in 
  let l = separate (fun s -> Str.string_match reg_big s 0) n1 (List.flatten (l :: ls)) in
  let ll = List.map (function (title, x :: xs) -> title, List.map (function (title, x :: xs) -> title, separate (fun x -> Str.string_match (Str.regexp ".+T Bit") x 0 || Str.string_match (Str.regexp_string "tion") x 0 || Str.string_match (Str.regexp_string "on") x 0) x xs | _ -> failwith importation_error) (separate (fun s -> Str.string_match reg_table s 0) x xs) | _ -> failwith importation_error) l in

  let ll = 
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
          let x1 :: x2 :: l = Str.split (Str.regexp " +") s in
          (x1, x2, List.exists ((=) "Privileged") l) :: acc)))) 
        []
        (("", ("", l2) :: l3) :: l4)
    | _ -> failwith importation_error in
  let _ = ignore ll in
  let l1, l2 = ll in 
(*  let () = Printf.printf "LLLLLLLLL %d %d\n%!" (List.length l1) (List.length l2) in*)
  ll

)

  let pos t = t.pos
  let c_code t = t.c_code

  let close_in t = P.close_in t.ic
end

let str_match r s l = 
  if Str.string_match (Str.regexp r) s 0 then
    Some (List.map (fun i -> Str.matched_group i s) l)
  else 
    None

module type C_PARSE = 
sig
  val c_of_file : string (* filename *) -> Cabs.definition list
  val c_of_program : string (* program written in C language *) -> Cabs.definition list
  val preprocess : string (* program written in C language *) -> string list (* program written in C language *)
  val expand_line_space : string list -> string list
end

module C_parse : C_PARSE = 
struct
  let c_of_file fic : Cabs.definition list = 
    let ic = open_in_bin fic in
    let v = Parser.file Lexer.initial (Lexer.init "#" ic) in
    let _ = close_in ic in
    v

  let cmd_file c_of_file suf str = 
    let fic = ((* FIXME let-réduire *) let temp_dir = "." in Filename.temp_file ~temp_dir) "test" suf in
    let oc = open_out fic in
    let () = Printf.fprintf oc "%s\n" str in
    let () = close_out oc in
    let v = c_of_file fic in
    let () = Unix.unlink fic in
    v

  let c_of_program str : Cabs.definition list = 
    let fic = ((* FIXME let-réduire *) let temp_dir = "." in Filename.temp_file ~temp_dir) "test" "" in
    let oc = open_out fic in
    let () = Printf.fprintf oc "%s\n" str in
    let () = close_out oc in
    let v = c_of_file fic in
    let () = Unix.unlink fic in
    v

  let process f s = 
    let ic, oc = 
      Unix.open_process f in
    let () = output_string oc s in
    let () = close_out oc in
    let rec aux l = 
      match try Some (input_line ic) with _ -> None with
        | None -> List.rev l
        | Some s -> aux (s :: l) in
    let l = aux [] in
    let _ = Unix.close_process (ic, oc) in
    l

  let preprocess = 
    process (Printf.sprintf "gcc -E -U__GNUC__ /dev/stdin")

  let preprocess = 
    cmd_file (fun fic -> 
      let ic = Unix.open_process_in (Printf.sprintf "gcc -E -U__GNUC__ %s" fic) in
      let rec aux l = 
	match try Some (input_line ic) with _ -> None with
          | None -> List.rev l
          | Some s -> aux (s :: l) in
      let l = aux [] in
      let _ = Unix.close_process_in ic in
      l
    ) ".c"

  let expand_line_space l =
    snd
      (List.fold_left (fun (pos1, acc) s ->
	match str_match "# \\([0-9]+\\) " s [1] with
          | Some [n] -> 
	    let pos2 = int_of_string n in
	    let rec aux pos1 acc = 
	      if pos1 = pos2 then 
		pos1, acc
	      else
		aux (succ pos1) ("" :: acc) in
	    aux pos1 acc
          | _ -> 
	    succ pos1, s :: acc) (1, []) l)
end


let display_dec = false
let display_c = true

module States = struct
  type t = 
    | Tiret
    | Pos of int
    | Range of int * int
end

module T_bit = struct
  type t = 
    | Tiret
    | Zero
    | One
    | One_Zero
    | Borrow
    | Carry
    | LSB
    | MSB
    | Overflow
    | Result_of_
    | Test
    | Underflow
    | Empty
end

type inst_code = 
  | I_0
  | I_1
  | I_n
  | I_m
  | I_i
  | I_d

type decoder_line = 
    { before_code : string
    ; inst_code : (inst_code * int) list
    ; states : States.t
    ; t_bit : T_bit.t } 

type decoder_rep = 
  | Dec_usual of decoder_line
  | Dec_dash of bool option

type dec_title = (** For the following cases, the words after "Menu" is the words we have to append (in front of the usual "Format, Summary of Operation, Instruction Code, Execution States, T Bit") to get the real title *)
  | Menu (* [ "Format" ; "Summary of Operation" ; "Instruction Code" ; "Execution States" ; "T Bit" ] *)

  (** 9.25 include to 9.47 include, 9.34 9.44 are exceptions *)
  | Menu_PR
  | Menu_NO_PR
  | Menu_NO_SZ

type decoder = 
    { dec_tab : (decoder_rep * string list) list (** *)
    ; dec_inst_ty : string
    ; dec_title : dec_title
    ; dec_title_long : string
    ; dec_other : string * string * string list }

type raw_c_code = 
    { init : string list (* WARNING [init] is unused *)
    ; code : Cabs.definition list (** representation of the C pseudocode, natural order : first element in the list = first line *) }

type 'a instruction = 
    { explanation_desc : string list (** information present in the part "description" *) 
    ; explanation_other : string list (** information eventually present after the C code *)


    ; decoder : decoder
    ; c_code : 'a
    ; position : int }

type 'a manual = 
    { entete : 'a (** piece of C code present at the beginning of section 9 *) 
    ; section : 'a instruction list }


let preprocess_c : string list manual -> raw_c_code manual = fun m -> 
  let (pos, code), l_pos =
    List.fold_left (fun ((pos, acc_s), l_pos) l -> 
      List.fold_left (fun (pos, acc_s) s -> succ pos, Printf.sprintf "%s%s\n" acc_s s)
        (pos, acc_s) l, pos :: l_pos) ((0, ""), [])
      (m.entete :: List.map (fun i -> i.c_code) m.section) in

  let _, (_, l, ll) =
    List.fold_left 
      (fun (pos, (l_pos, acc_l, acc_ll)) s -> 
	pred pos, 
	match l_pos with
	  | [] -> 
	    [], s :: acc_l, acc_ll
	  | x :: xs -> 
	    if pos = x then
	      xs, [s], acc_l :: acc_ll
	    else
	      l_pos, s :: acc_l, acc_ll) 
      (pos, (l_pos, [], [])) 
      (C_parse.expand_line_space (C_parse.preprocess code)) in

  let mk_code l = 
    { init = l
    ; code = C_parse.c_of_program (List.fold_left (Printf.sprintf "%s%s\n") "" l) } in

  { entete = mk_code l ; section = List.map2 (fun l i -> { i with c_code = mk_code l }) ll m.section }

(** We regroup a line written into a multi-lines into a single block. Heuristic used : we consider as a member of a previous line, any line beginning with a space. *)
(* Remark : we can replace the "Assert_failure" by a "[]" *)
let structure_line = 
  let rec aux l = function 
    | x :: xs -> 
      
      let rec aux2 l_bl = function
        | x :: xs when x.[0] = ' ' -> aux2 (x :: l_bl) xs
        | xs -> List.rev l_bl, xs in
      let l_bl, xs = aux2 [] xs in
      if xs = [] then
        List.rev ((x, l_bl) :: l)
      else
        aux ((x, l_bl) :: l) xs
    | _ -> assert false in
  aux []


(** Simplify a string (only formed with : 0, 1, n, m, i, d) into a list composed of the character and the number of occurences it appears after *)
let list_of_string_01nmid s = 
  let lg = String.length s in
  let rec aux l n = 
    if n = lg then
      List.rev l
    else
      let rec aux2 i = 
        if n + i = lg then
          i
        else if s.[n] = s.[n + i] then
          aux2 (succ i)
        else
          i in
      let i = aux2 1 in
      aux (((match s.[n] with 
        | '0' -> I_0
        | '1' -> I_1
        | 'n' -> I_n
        | 'm' -> I_m
        | 'i' -> I_i
        | 'd' -> I_d
        | _ -> assert false (* by definition of [Str.matched_group], we can prove that this case is never reached *)
      ), i) :: l) (n + i) in
  aux [] 0

module S_map = Map.Make (struct type t = string let compare = compare end)

module List = 
struct
  include List

  let init f =
    let rec aux l n = 
      if n = 0 then
        l
      else
        let n = pred n in
        aux (f n :: l) n in
    aux [] 
end

module P = 
struct

  module E = 
  struct

    type mode = Fiq | Irq | Svc | Abt | Und | Usr | Sys
      
    type size = Byte | Half | Word

    type exp =
      | Num of string
      | Bin of string
      | Hex of string
      | Float_zero
      | If_exp of exp * exp * exp
      | Fun of string * exp list
      | BinOp of exp * string * exp
      | CPSR
      | SPSR of mode option
      | Reg of exp * mode option
      | Var of string
      | Range of exp * range
      | Unaffected
      | Unpredictable_exp
      | Memory of exp * size
      | Coproc_exp of exp * string * exp list
      (*| Member_of of exp * string*)

    and range =
      | Bits of string * string
      | Flag of string * string (* 2nd arg is the name used like "Flag" or "bit" *)
      | Index of exp

    type type_param = Tint | Tlong | Tfloat | Tdouble

    type inst =
      | Block of inst list
      | Let of string * (type_param * string) list * inst list * inst
      | Unpredictable
      | Affect of exp * exp
      | If of exp * inst * inst option
      | Proc of string * exp list
      | While of exp * inst
      | Assert of exp
      | For of string * string * string * inst
      | Coproc of exp * string * exp list
      | Case of exp * (string * inst) list * inst option (* default *) 
      | Return of exp

    type ident = {
      iname : string;
      iparams : string list;
      ivariant : string option }

    type kind =
      | InstARM (* instruction on 32 bits *)
      | InstThumb (* instruction on 16 bits *)
      | Mode of int (* addressing mode *)

    type prog = {
      pref : string; (* chapter in the ARM documentation (e.g. A4.1.20) *)
      pkind : kind;
      pident : ident;
      pidents : ident list; (* alternative idents *)
      pinst : inst }
  end

  module D =
  struct 
    type lightheader = LH of int list * string

    type pos_contents =
      | Nothing
      | Value of bool                  (* false -> 0, true -> 1 *)
      | Param1 of char                 (* e.g. S *)
      | Param1s of string              (* e.g. mmod *)
      | Range of string * int * int    (* length position, e.g. Rn 4 0 *)
      | Shouldbe of bool               (* false -> SBZ, true -> SBO *)
  end
end

let _ = 
  let module S = SH4_section in

  let t = 
    match try Some Sys.argv.(1) with _ -> None with
      | Some s -> S.init s
      | None -> S.init_channel stdin in

  (** These regexp characterize the end of any C code present in the documentation *)
  let accol_end = Str.regexp " *} *" (* C code usually end with a '}' delimiter *) in
  let comment = Str.regexp " */\\*.*\\*/ *" (* a line containing C comment like /* */ *) in

  let matched_group_i n s = int_of_string (Str.matched_group n s) in
  let matched_group_t n s = let open T_bit in
    match Str.matched_group n s with
      | "\226\128\148" -> Tiret
      | "0" -> Zero
      | "1" -> One
      | "1/0" -> One_Zero
      | "Borrow" -> Borrow
      | "Carry" -> Carry
      | "LSB" -> LSB
      | "MSB" -> MSB
      | "Overflow" -> Overflow
      | "Result of" -> Result_of_
      | "Test" -> Test
      | "Underflow" -> Underflow 
      | "" -> Empty
      | _ -> failwith importation_error in

  let rec aux t l_section =
    match S.input_instr t with 
      | Last l_no_param -> 

        List.rev l_section
      | Next (l, t) -> 
        let l = List.flatten (List.rev l) in
        
        let decoder, l = (** [l1] contains the information between the beginning of the section and the line "Description" *)
          let l1, _, l = split_beg ((=) "Description") l in 
          
          match split_beg ((=) "") l1 with
            | [], _, _ | _ :: [], _, _ -> failwith importation_error
            | x1 :: x2 :: l1, _, l2 -> 
                (** Example : [x1] and [x2] contains
                    - "9.1 [whitespace] ADD [whitespace] ADD binary [whitespace] Arithmetic Instruction"
                    - " [whitespace] Binary Addition"
                *)

          let m l = l_match (List.map (function x1, x2 -> Str.regexp x1, x2) l) in

          let contains_instruction x = m [ "\\(.+\\) +\\([A-Z][a-z]+\\)-?\\([A-Z][a-z]+\\)* Instruction", x ] in
          
          let (x1, x2), inst_ty = match () with
            | _ when contains_instruction x1 -> 
              let inst_ty = Str.matched_group 2 x1 ^ try "-" ^ Str.matched_group 3 x1 with _ -> "" in
              let x1, x2 = Str.matched_group 1 x1, x2 in
              (** In this part, we detect if the sequence "Delayed Branch Instruction" is present. *)
              (* (* to be completed *) let _ = 
                      match inst_ty with
                        | "Branch" -> 
                          (if m [ "\\(.+\\) +Delayed Branch Instruction", x2 ] then
                              Printf.printf "[[[[[\n%s\n]]]]]\n%!" (Str.matched_group 1 x2)
                           else 
                              ())
                        | _ -> () in*)
                (x1, x2), inst_ty
            | _ when contains_instruction x2 -> 
              (x1, Str.matched_group 1 x2), Str.matched_group 2 x2 ^ (try "-" ^ Str.matched_group 3 x2 with _ -> "")
            | _ -> failwith importation_error in 
          
          match (** suppress the block of eventually empty lines at the beginning and the end *)
            let f x = del_line (List.rev x) in f (f l2)
          with
            | [] | _ :: [] -> failwith importation_error
            | x_exe :: header :: l2 ->

          let dec_title = (** we rewrite correctly the title of the array *)
            match () with 
              | _ when m [ "^ *Execution *$", x_exe ] -> 
                (match Str.split (Str.regexp "  +") header with
                  | [ "Format" ; "Summary of Operation Instruction Code" ; "States" ; "T Bit" ] 
                  | [ "Format" ; "Summary of Operation" ; "Instruction Code" ; "States" ; "T Bit" ] 
                  | [ "Format" ; "Summary of Operation" ; "nstruction Code" ; "States" ; "T Bit" ] -> Menu
                  | [ "PR Format" ; "Summary of Operation Instruction Code" ; "States" ; "T Bit" ] 
                  | [ "PR" ; "Format" ; "Summary of Operation Instruction Code" ; "States" ; "T Bit" ] 
                  | [ "PR" ; "Format" ; "Summary of Operation" ; "Instruction Code" ; "States" ; "T Bit" ] -> Menu_PR
                  | [ "No. PR Format" ; "Summary of Operation Instruction Code" ; "States" ; "T Bit" ] -> Menu_NO_PR
                  | _ -> failwith importation_error)
              | _ when m [ "^ *Summary of +Execution *$", x_exe ] -> 
                      (** This case only applies to 9.37 and 9.38. Hopefully, the number of fields and the type of the data of each column are the same in both cases. *)
                (match String.sub x1 0 4 with "9.37" -> Menu_NO_SZ | "9.38" -> Menu_NO_PR | _ -> failwith importation_error)
              | _ -> failwith importation_error in

          let dec_tab = 
            List.map (fun (s, l2) -> 
              (if m [ "\\(.+\\) +\\([01nmid][01nmid][01nmid][01nmid][01nmid][01nmid][01nmid][01nmid][01nmid][01nmid][01nmid][01nmid][01nmid][01nmid][01nmid][01nmid]\\) +\\([0-9]+\\)\\(\226\128\147\\([0-9]+\\)\\)? *\\(.*\\)", s ] then
                  Dec_usual { before_code = Str.matched_group 1 s
                            ; inst_code = list_of_string_01nmid (Str.matched_group 2 s)
                            ; states = (let open States in
                                            (match try Some (matched_group_i 5 s) with _ -> None with
                                              | None -> fun x -> Pos x
                                              | Some i_end -> fun i_beg -> Range (i_beg, i_end)) (matched_group_i 3 s))
                            ; t_bit = matched_group_t 6 s }
               else
                  let l_dash = Str.split (Str.regexp "  +") s in
                  let o, xs = 
                    match l_dash with
                      | ("0" | "1" as b) :: xs -> Some (b = "1"), xs
                      | xs -> None, xs in
                  if List.for_all ((=) "\226\128\148" (* dash symbol "-" *)) xs then
                    Dec_dash o
                  else
                    failwith importation_error), l2
                      
            ) (let l2 = structure_line l2 (* Remark : if [l2] is empty, it is an [importation_error] *) in
               match String.sub x1 0 4 with
                 | "9.31" -> (match l2 with x1 :: x2 :: _ -> [x1; x2] | _ -> failwith importation_error)
                 | "9.55" 
                 | "9.64" 
                 | "9.65" -> (match l2 with x :: _ -> [x] | _ -> failwith importation_error)
                 | _ -> l2) in

          { dec_other = (x1, x2, l1) 
          ; dec_title = dec_title 
          ; dec_title_long = header
          ; dec_tab = dec_tab 
          ; dec_inst_ty = inst_ty }, l in

        let l2, _, l = split_beg ((=) "Operation") l in (** [l2] contains the information between the line "Description" and the line "Operation" *)
        let l3, n, l = split_end (fun x -> List.exists (fun r -> Str.string_match r x 0) [ accol_end; comment ]) l in (** [l3 @ [n]] contains the C program between the line "Operation" and some human language information we are not interested *)
        let c_code = 
          ((match decoder.dec_other with
              | (x1, _, _) when (match String.sub x1 0 4 with "9.50" | "9.92" -> true | _ -> false) -> 

                let r_bank = Str.regexp ".*_BANK" in
                let r_accol_end = Str.regexp ".*}" in
                let replace c_code =
                  let l1, n0, _ :: ll = split_beg (fun x -> Str.string_match r_bank x 0) c_code in
                  let l, n1, l2 = split_beg (fun x -> Str.string_match r_accol_end x 0) ll in
                  l1 @ List.flatten (
                    List.init (fun n -> List.map (Str.global_replace (Str.regexp "R._BANK") (Printf.sprintf "R%d_BANK" n)) ([n0] @ l @ [n1; ""])) 8), l2 in
                fun c_code -> 
                  let l1, l2 = replace c_code in
                  let l2, l3 = replace l2 in
                  l1 @ l2 @ l3

              | _ -> fun x -> x) (l3 @ [n])) in

        aux t ({ position = S.pos t 
               ; explanation_desc = l2 
               ; c_code = c_code

               ; explanation_other = l 
               ; decoder = decoder } :: l_section) in


  let manual = preprocess_c { entete = S.c_code t ; section = aux t [] }  in

  let () = output_value stdout manual in
  let () = exit 0 in

  let s_map = ref S_map.empty in
  begin
    if false && display_c then
      begin 
        List.iter (fun s -> Printf.printf "%s\n" s) manual.entete.init;
      end; 
    List.iter (fun sec -> 
      begin 
        if false && display_c then
          begin
            Printf.printf "/* 9.%d */\n" sec.position;
            Printf.printf "%s\n%!" (List.fold_left (Printf.sprintf "%s%s\n") "" sec.c_code.init);
          end;
        if display_c then
          begin
          match sec.decoder.dec_title with
            | Menu ->
            (*Printf.printf "/* 9.%d */" sec.position;*)

            (** algorithm for coupling the line present in the decoder and the pseudo code *)
            let n1 = List.fold_left (fun acc -> function Dec_usual _, _ -> succ acc | _ -> acc) 0 sec.decoder.dec_tab (** number of line in the array *)
            and n2 = List.length sec.c_code.code (** number of function defined in C *) in
            let () = if n1 = n2 then () else assert false in

              (** test to verify that every function has a name in uppercase ('_' and number are allowed) *)
            List.iter (let module C = Cabs in
                       function 
                         | C.FUNDEF ((_, (s, _, _, _)), _, _, _) -> let m r = Str.string_match (Str.regexp r) s 0 in
                           match () with 
                             | _ when m "[0-9_A-Z]+$" -> ()
                             | _ -> assert false (*Printf.printf "%s\n%!" s*) ) sec.c_code.code
            | Menu_PR -> 
              begin
              Printf.printf "/* 9.%d PR */" sec.position;

              (** test to verify that every function has a name in uppercase ('_' and number are allowed) *)
              let n1 = List.fold_left (fun acc -> function Dec_usual _, _ -> succ acc | _ -> acc) 0 sec.decoder.dec_tab (** number of line in the array *)
              and n2 = 
              List.fold_right (let module C = Cabs in
                         function 
                           | C.FUNDEF ((_, (s, _, _, _)), _, _, _) -> let m r = Str.string_match (Str.regexp r) s 0 in
                             match () with 
                               | _ when m "[0-9_A-Z]+$" -> succ
                               | _ when m "[0-9_a-z]+$" -> (fun x -> x)
                               | _ -> assert false ) sec.c_code.code 0 in
              let () = if n1 = n2 then () else Printf.printf "/* %d %d */\n" n1 n2 in
              ()
              end
            | Menu_NO_PR -> 
              begin
              Printf.printf "/* 9.%d NOPR */" sec.position;

              (** test to verify that every function has a name in uppercase ('_' and number are allowed) *)
              List.iter (let module C = Cabs in
                         function 
                           | C.FUNDEF ((_, (s, _, _, _)), _, _, _) -> let m r = Str.string_match (Str.regexp r) s 0 in
                             match () with 
                               | _ when m "[0-9_A-Z]+$" -> ()
                               | _ when m "[0-9_a-z]+$" -> Printf.printf "%s\n%!" s 
                               | _ -> assert false ) sec.c_code.code;
              end
            | Menu_NO_SZ -> 
              begin
              Printf.printf "/* 9.%d NOSZ */" sec.position;

              (** test to verify that every function has a name in uppercase ('_' and number are allowed) *)
              List.iter (let module C = Cabs in
                         function 
                           | C.FUNDEF ((_, (s, _, _, _)), _, _, _) -> let m r = Str.string_match (Str.regexp r) s 0 in
                             match () with 
                               | _ when m "[0-9_A-Z]+$" -> ()
                               | _ when m "[0-9_a-z]+$" -> Printf.printf "%s\n%!" s 
                               | _ -> assert false ) sec.c_code.code;
              end

          end;

        if display_dec then
          List.iter (function
            | Dec_usual line, _ ->
              begin
                Printf.printf "#%s#\n" ((*List.fold_left (Printf.sprintf "%s%s|") "" *) sec.decoder.dec_title_long);
                Printf.printf "|%s|\n" line.before_code ;
                    (*List.iter (fun s -> Printf.printf "|%s|\n" s) l2;
                Printf.printf "\n";*)
              end
            | Dec_dash _, _ -> ()) sec.decoder.dec_tab;

      end) manual.section;

    Printf.printf "%!";
  end
