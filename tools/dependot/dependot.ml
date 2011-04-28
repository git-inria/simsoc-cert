(* Construction of a dot file from Makefile dependance specifications *)
(* Transitive dependencies are removed                                *)
(* Author: JF Monin, Verimag and University Joseph Fourier, Grenoble  *)
(* Licence: CeCILL, http://www.cecill.info/index.en.html              *)
(* 2005 - 2011 *)

module StringSet = Set.Make (struct type t = string let compare = compare end)

module StringMap = Map.Make (struct type t = string let compare = compare end)

(* ------------------------------------------------------------ *)
(* READING *)

let add_targ_set key v m =
  try 
    let v0 = StringMap.find key m in
    StringMap.add key (StringSet.union v0 v) (StringMap.remove key m)
  with Not_found -> StringMap.add key v m

let addset a x s = 
  let b = Filename.chop_extension x in
  if a = b then s else StringSet.add b s

let rec k_add_targ buf add targs s r  =
   if r.[String.length r - 1] = '\n' then 
     if s = "" then targs else add s targs
   else let targs1 = add s targs in 
   bouffe buf add targs1
and bouffe buf add l = Scanf.bscanf buf "%s%[\n ]" (k_add_targ buf add l)

(* Scans the whole input (buf), line by line *)
let rec ligne buf add empty base = 
  let x = Scanf.bscanf buf "%s@:%[ ]" (fun s r -> s) in
  if x = "" then base 
  else 
    let bx = Filename.chop_extension x in
    let l = bouffe buf (add bx) empty in
    ligne buf add empty (add_targ_set bx l base)

(* let buf = Scanf.Scanning.from_file "exemple.depend" *)
let buf_in = Scanf.Scanning.stdib

(* Building the buffer *)

(* ocamldep puts  '\' for next line continuation *)
let rec take_not_slash buf accu =
  let s = Scanf.bscanf buf "%[^\\]" (fun s -> s) in
  remove_slash_nl buf (accu ^ s) 
and remove_slash_nl buf accu = 
  try 
    let _sl = Scanf.bscanf buf "%c" (fun c -> c) in
    let c = Scanf.bscanf buf "%c" (fun c -> c) in
    if c = '\n' then take_not_slash buf accu
    else take_not_slash buf (Printf.sprintf "%s\\%c" accu c)
  with End_of_file -> accu

let buf = Scanf.Scanning.from_string (take_not_slash buf_in "")

(* Result of reading: Data base of raw data *)

let base = ligne buf addset StringSet.empty StringMap.empty

(* ------------------------------------------------------------ *)

(* TODO : circular dependendies forbidden and not checked *)

(* ------------------------------------------------------------ *)
(* COMPUTING THE INTENDED GRAPH *)

let newroots src targs (roots,alltg) = 
  let alltg = StringSet.union targs alltg in
  let roots = StringSet.diff roots targs in
  let roots =
    if StringSet.mem src alltg then roots else StringSet.add src roots in
  roots, alltg

let roots,alltg =
  StringMap.fold newroots base (StringSet.empty,StringSet.empty)

let sm_find x m = try StringMap.find x m with Not_found -> StringSet.empty

let print_set msg s = 
  Printf.printf "%s = " msg ;
  StringSet.iter (fun x -> Printf.printf "%s; " x) s;
  Printf.printf "\n" 

(* desc = trans closure of base/visited, asc = idem for base^(-1) *)
let rec asc_desc visited asc desc todo =
  if todo = StringSet.empty then (asc,desc)
  else 
    let x = StringSet.choose todo in
    let targs = sm_find x base in
    let visited_targs = StringSet.inter visited targs in
    let new_targs = StringSet.diff targs visited_targs in
    let todo = StringSet.union new_targs todo in
    let todo = StringSet.remove x todo in
    let visited = StringSet.add x visited in

    let asc_x = sm_find x asc in

    (* adding x as an ancestor of y *)
    let add_asc y asc =
      let asc_y = sm_find y asc in
      StringMap.add y (StringSet.add x asc_y) asc in
    (* adding x as an ancestor of all its successors *)
    let asc = StringSet.fold add_asc targs asc in

    (* adding y as a descendant of a *)
    let add_desc y a desc =
      let desc_a = sm_find a desc in
      StringMap.add a (StringSet.add y desc_a) desc in
    (* adding y as a descendant of all ancestors of de x *)
    let add_desc_asc_x y desc = StringSet.fold (add_desc y) asc_x desc in
    (* adding successors of x as descendant of all its ascendants *)
    let desc = StringSet.fold add_desc_asc_x targs desc in
    (* adding y as a descendant a x *)
    let add_desc_x y desc = add_desc y x desc in
    (* adding all successors of x as descendant of x *)
    let desc = StringSet.fold add_desc_x targs desc in
    asc_desc visited asc desc todo

let asc_m,desc_m = asc_desc StringSet.empty StringMap.empty StringMap.empty roots

let asc x = sm_find x asc_m
let desc x = sm_find x desc_m

let rec simplify visited simplemap todo =
  if todo = StringSet.empty then simplemap
  else 
    let x = StringSet.choose todo in
    let targs = sm_find x base in
    let visited_targs = StringSet.inter visited targs in
    let new_targs = StringSet.diff targs visited_targs in
    let todo = StringSet.union new_targs todo in
    let todo = StringSet.remove x todo in
    let visited = StringSet.add x visited in

    let is_new y = StringSet.is_empty (StringSet.inter (desc x) (asc y)) in
    let new_targs_x = StringSet.filter is_new targs in
    let simplemap = StringMap.add x new_targs_x simplemap in
    simplify visited simplemap todo

(* Result of the computation *)
let simplemap = simplify StringSet.empty base roots

(* ------------------------------------------------------------ *)
(* WRITING *)

(* The new version (April 2011) puts guillemets around names
   in order to allow path expressions with / and .. 
   (see dot manual)                                          
*)


let print_node x targs = 
  if StringSet.is_empty targs then ()
  else
    let y = StringSet.choose targs in
    Printf.printf "\"%s\" -> { \"%s\"" x y;
    StringSet.iter
      (fun z -> Printf.printf "; \"%s\"" z) (StringSet.remove y targs);
    Printf.printf " }\n"

let print_map m = 
  Printf.printf "DiGraph dependencies {\n";
  StringMap.iter print_node m;
  Printf.printf "}\n"

let _ = print_map simplemap
