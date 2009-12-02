(* 
#load "dynlink.cma";; 
#load "camlp4o.cma";; 
*)

let cin = open_in "ADC.txt"

(* Pour le test *)
let rec list_of_stream = parser
  | [< 'x; l = list_of_stream >] -> x :: l
  | [< >] -> []

(* REPERER les \n *)

let s = Stream.of_channel cin

let grrr = list_of_stream s

let ligne_titre_ref = "A4.1.2     ADC"
let l = input_line cin

let s = Stream.of_string l
let s = Stream.of_string ligne_titre_ref

type debop = Nodebop | Debop of string

let maju = parser 
  | [< ''A'..'Z' ; s >] -> s

let chiffre = parser 
  | [< ''0'..'9' ; s >] -> s

(* Identificateurs *)
let ident =
  let bu = Buffer.create 16 in 
  let rec ident_aux = parser
    | [< '  'a'..'z'| 'A'..'Z' | '0'..'9' as c; s >] -> 
        Buffer.add_char bu c; ident_aux s
    | [< >] -> Buffer.contents bu in
  let ident c s = Buffer.clear bu; Buffer.add_char bu c; ident_aux s in
  ident

let rec digidots = parser 
  | [< ''.' | '0'..'9' ; s  >] -> digidots s
  | [< '' ' >] -> ()

let rec opname = parser 
  | [< '' ' ; s >] -> opname s
  | [< ''A'..'Z' as c; s = ident c >] -> Debop(s)

let debop = parser
  | [< ''A'..'Z' ; () = digidots; s >] -> opname s
  | [< >] -> Nodebop

let x = debop s

let () = close_in cin
