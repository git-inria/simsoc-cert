(**
SimSoC-Cert, a Coq library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Parser for binary encoding of instructions
*)

(* 
#load "dynlink.cma";; 
#load "camlp4o.cma";; 
ocamlc -pp camlp4o
*)

module CT = Codetype

(* For testing *)
let rec list_of_stream = parser
  | [< 'x; l = list_of_stream >] -> x :: l
  | [< >] -> []


(* Identifiers *)
(* FIXME: ident2 now useless, to remove once confirmed *)
let ident, ident2 =
  let bu = Buffer.create 16 in 
  let rec ident_aux = parser
    | [< '  'a'..'z'| 'A'..'Z' | '0'..'9' | '_' as c; s >] -> 
        Buffer.add_char bu c; ident_aux s
    | [< >] -> Buffer.contents bu in
  let ident c s = Buffer.clear bu; Buffer.add_char bu c; ident_aux s in
  let ident2 c0 c1 s =
    Buffer.clear bu; Buffer.add_char bu c0; Buffer.add_char bu c1; ident_aux s in
  ident, ident2

(* Returns full line as string *)
let take_eol =
  let bu = Buffer.create 80 in 
  let rec aux = parser
    | [< ''\n' >] -> Buffer.contents bu
    | [< 'c; s >] -> Buffer.add_char bu c; aux s in
  let take_eol c s = Buffer.clear bu; Buffer.add_char bu c; aux s in
  take_eol

exception Empty_line_expected
let skip_empty_line = parser
    | [< ''\n' >] -> ()
    | [<  >] -> raise Empty_line_expected

(* integers *)

let valdigit c = int_of_char c - int_of_char '0'
let rec horner n = parser 
  | [< '  '0'..'9' as c; s >] -> horner (10 * n + valdigit c) s
  | [< >] -> n

(* Jumps to eol *)
let rec eat_eol = parser 
  | [< ''\n'; s >] -> ()
  | [< 'c; s >] -> eat_eol s

(* Reading a header *)
exception Not_header

(* Sequence of integers separated by 1 dot *)
let rec seqint1 = parser 
  | [< ''0'..'9'as c; n = horner (valdigit c); l = seqint  >] -> n, l
  | [< >] -> raise Not_header
and seqint = parser
  | [< ''.' ; s  >] -> let n, l = seqint1 s in n :: l
  | [< >] -> []

let rec title = parser 
  | [< '' ' ; s >] -> title s
  | [< ''A'..'Z' | 'a'..'z' as c; s = take_eol c >] -> s
  | [< >] -> raise Not_header

(* ex. A4.1.2 ADC  *)
type header = Header of char * int * int list * string

let end_header c = parser
  | [< n, l = seqint1; t = title >] -> Header (c, n, l, t)


let rec header = parser
  | [< '' ' ; s >] -> header s
  | [< ''A'..'Z' as c; s >] -> end_header c s

(* Sequence of integers separated by white spaces *)
exception Not_seq_int_spaces
let rec seqwhint1 c = parser 
  | [< n = horner (valdigit c); l = seqwhint  >] -> n :: l
  | [< >] -> raise Not_seq_int_spaces
and seqwhint = parser
  | [< '' ' ; s  >] -> seqwhint s
  | [< ''0'..'9'as c; s  >] -> seqwhint1 c s
  | [< >] -> []

(* Special case for fields tagged SBO and SBZ: 1 or several bits -> no simple algo *)
(* -> for 1 but replaced with !SBZ and !SBO *)
type code_contents = 
  B0 | B1 | Onebit of string | Several of string

let rec code_contents = parser
  | [< '' ' ; s >] -> code_contents s
  | [< '  '0'..'9' | 'a'..'z'| 'A'..'Z' | '_' | '!' as c; id = ident c >] -> 
      if c = '!' then Onebit (String.sub id 1 (String.length id -1 )) else
	match id with
	  | "0" -> B0
	  | "1" -> B1
	  | "mmod" -> Onebit (id)
	  | _ -> if String.length id = 1 then Onebit (id) else Several (id)
	    
let rec seq_contents = parser
  | [< t = code_contents; l = seq_contents >] -> t :: l
  | [< >] -> []

type instruction = Instruction of header * int list * code_contents list

let instruction = parser
  | [< h = header;
       li = seqwhint;
       () = skip_empty_line;
       lc = seq_contents;
       () = skip_empty_line
    >] -> Instruction (h, li, lc)

let rec instructions_list = parser
  | [< o = instruction; l = instructions_list >] -> o :: l
  | [< >] -> []

(* For debugging the ARM doc: more robust and provides the reversed result
   so we can see the last successfully parsed instruction
 *)
let rec debug_instructions l s = 
  match (try Some (instruction s) with _ -> None) with
    | Some o -> debug_instructions (o :: l) s
    | None -> l

(* Mapping code_contents to bit numbers *)

type map = CT.pos_contents array

(* Inconsistent (expected index, position list, contents list, map) *)
exception Inconsistent of int * int list * code_contents list * map

(* Checks
  - the position list should decrease from 31 to 0 without hole
  - the consistency of the position list with code_contents list
*)
let build_map lint lcont =
  let map = Array.make 32 (CT.Nothing) in
  let rec loop exp lint lcont =
    (match lint with 
      | x :: _ when x <> exp -> raise (Inconsistent (exp, lint, lcont, map))
      | _ -> ());
    match lint, lcont with
      | x :: y :: lint, Several(id) :: lcont -> 
	  if x<=y then raise (Inconsistent (exp, lint, lcont, map)) else
	    let n = x - y  in
	    for i = 0 to n do map.(y + i) <- CT.Range (id, n+1, i) done;
	    loop (y-1) lint lcont
      | x :: lint,  B0 :: lcont  ->
	  map.(x) <- CT.Value (false); 
	  loop (x-1) lint lcont
      | x :: lint,  B1 :: lcont  ->
	  map.(x) <- CT.Value (true);
	  loop (x-1) lint lcont
      | x :: lint,  Onebit (id) :: lcont  -> 
	  map.(x) <- if String.length id = 1 then CT.Param1 (id.[0]) else CT.Param1s (id);
	  loop (x-1) lint lcont
      | [],  [] -> ()
      | _, _ -> raise (Inconsistent (exp, lint, lcont, map))
  in 
  loop 31 lint lcont;
  map

let light = function Header (_, _, l, s) -> (CT.LH (l, s))

let rec maplist = function
  | [] -> []
  | Instruction (h, li, lc) :: l -> (light h, build_map li lc) :: maplist l

exception No_exc

type 'a result = OK of 'a | Exn of exn

(* For debugging the ARM doc *)
let rec debug_maplist a = function
  | [] -> No_exc, a
  | Instruction (h, li, lc) :: l ->
       match (try OK (build_map li lc) with e -> Exn(e)) with
	 | Exn (e)  -> e, a
	 | OK (m) -> debug_maplist ((light h, m) :: a) l


(* Returns the intended list of maps,
  where each map is an array of length 32 *)
let main s : CT.maplist =
  let linst = instructions_list s in
  let lmap = maplist linst in
  lmap

let () = 
  let l = main (Stream.of_channel stdin) in
  output_value stdout l

(*

(* tests *)


let () = close_in cin
let cin = open_in "ADCbin.txt"
let s = Stream.of_channel cin
let Instruction(_, lint, lcont) = instruction s
let m = build_map lint lcont

let () = close_in cin
let cin = open_in "bincodeV6.txt"
let s = Stream.of_channel cin
let linst = instructions_list s
let lmap = debug_maplist [] linst

let () = close_in cin
let cin = open_in "bincodeV6.txt"
let s = Stream.of_channel cin
let linst = instructions_list s
let lmap = maplist linst
let () = close_in cin

let bidon = 0

*)
