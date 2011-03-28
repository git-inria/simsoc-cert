(**
SimSoC-Cert, a toolkit for generating certified processor simulators
See the COPYRIGHTS and LICENSE files.

Main program of the pretty printer of the CompCert type [AST.program fundef type].
*)

open Printf

module Camlcoq = 
struct
  include Camlcoq

  let ascii_of_char c = 
    let f = 
      let i = Char.code c in
      fun n -> (i lsr n) land 1 <> 0 in
    Ascii.Ascii (f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7)

  let coqstring_of_camlstring s = 
    let rec aux n acc = 
      if n < 0 then
        acc
      else
        aux (pred n) (String0.String (ascii_of_char s.[n], acc)) in
    aux (pred (String.length s)) String0.EmptyString
end

module S =
struct
  type t = string
      
  let of_string = Camlcoq.camlstring_of_coqstring
  let rindex _ c s = match try Some (String.rindex s c.[0]) with _ -> None with None -> None | Some n -> Some (Camlcoq.nat_of_camlint (Int32.of_int n))
  let empty = ""
  let length s = (Camlcoq.nat_of_camlint (Int32.of_int (String.length s)))
  let make n c = String.make (Camlcoq.camlint_of_nat n) (Camlcoq.char_of_ascii c)
  let append = (^)
end

module U =
struct
  open Camlcoq
    
  let string_of_nat n =
    sprintf "%d" (camlint_of_nat n)
  let string_of_positive n = 
    sprintf "%ld" (camlint_of_positive n)
  let string_of_Z n = 
    sprintf "%ld" (camlint_of_z n)
  let replace =
    let reg = Str.regexp "\\$\\| " in
    let open Datatypes in
        function
          | "end" -> Coq_pair ("_end", Some "end")
          | s -> let s2 = Str.global_replace reg "_" s in Coq_pair (s2, if s2 = s then None else Some s)

  let name p = 
    match try Some (Hashtbl.find Camlcoq.string_of_atom p) with Not_found -> None with
      | None -> None
      | Some s -> Some (replace s)
end

module B = 
struct
  type t = { n : int ; buf : Buffer.t }
      
  let empty _ = { n = 0 ; buf = Buffer.create 1000 } 
    
  let print s t =
    let () = bprintf t.buf "%s" s in
    { t with n = t.n + String.length s }
      
  let print_newline t =
    let () = bprintf t.buf "\n" in
    { t with n = 0 }
      
  let pos t = Camlcoq.nat_of_camlint (Int32.of_int t.n)

  let add_buffer t1 t2 = 
    let () = Buffer.add_buffer t1.buf t2.buf in
    { t1 with n = t2.n }
end

module R = RawCoq_Csyntax.Main (S) (U) (B)

let to_buffer csyntax = (R.program_fundef_type csyntax).B.buf
