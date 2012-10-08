
open Printf;;
open Syntaxtype;;

let list sep f =
  let rec aux b = function
    | [] -> ()
    | [x] -> f b x
    | x :: xs -> bprintf b "%a%s%a" f x sep aux xs
  in aux;;

let int b s = bprintf b "%d" s;;

let print_syntax b syn =
  let aux1 b tk =
    match tk with
      | Const s -> bprintf b "%s" s
      | Param s -> bprintf b "<%s>" s
      | OptParam (s, None) -> bprintf b "{%s}" s
      | OptParam (s1, Some s) -> bprintf b "{%s<%s>}" s1 s
      | PlusMinus -> bprintf b "+/-"
  in
  let rec aux2 b var =
    match var with
      | [] -> bprintf b ""
      | tk::tks -> aux1 b tk; aux2 b tks
  in
  let aux3 b ((lst_i, str), lst_var) =
    bprintf b "A%a %s\n" (list "." int) lst_i str;     
    (list "\n" aux2) b lst_var
  in 
    (list "\n" aux3) b syn
;;

let open_file fn =
  try open_in fn with Sys_error s -> prerr_endline s; exit 1;;

let main () =
  let b = Buffer.create 100000 in
  let syn = input_value (open_file "../arm6/arm6syntax.dat") in
    print_syntax b syn;
    let conv = open_out ("arm6syntaxconvert.txt") in
      Buffer.output_buffer conv b; close_out conv
;;

let _ = main ();;
