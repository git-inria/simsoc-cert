(**
SimSoC-Cert, a library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Replace each instruction with n mode cases by n instructions with one 1 specific
mode case.
*)

open Ast;;
open Dec;;
open Codetype;;

(* Like List.map2, but for arrays *)
(* Code based on the OCaml implementation of Array.map *)
let array_map2 f a b =
  let l = Array.length a in
    assert (l = Array.length b);
    if l = 0 then [||] else
      begin
        let r = Array.create l (f (Array.unsafe_get a 0) (Array.unsafe_get b 0)) in
          for i = 1 to l - 1 do
            Array.unsafe_set r i (f (Array.unsafe_get a i) (Array.unsafe_get b i))
          done;
          r
      end;;

(* Sequential composition of two instructions *)
let merge_inst (i: inst) (m: inst) = match m, i with
  | Block l1, Block l2 -> Block (l1@l2)
  | Block l, i -> Block (l@[i])
  | i, Block l -> Block (i::l)
  | i, j -> Block([i; j]);;

(* Compose a mode ident with an instruction ident *)
let merge_ident (i: ident) (m: ident) =
  assert (m.ivariant = None);
  {iname = m.iname^"  "^i.iname;
   iparams = m.iparams @ i.iparams;
   ivariant = i.ivariant};;

(* return a new "prog" obtained by combining an instruction prog with a mode prog *)
let merge_prog (i: prog) (m: prog) =
  {pref = i.pref^", "^m.pref;
   pkind = Inst;
   pident = merge_ident i.pident m.pident;
   pidents = i.pidents @ m.pidents;
   pinst = merge_inst i.pinst m.pinst};;

(* used only for debug *)
let print_pos_contents pc =
  let print_bool b = print_string (if b then "true" else "false") in
  match pc with
  | Nothing -> print_string "Nothing"
  | Value v -> print_string "Value "; print_bool v
  | Param1 c -> print_string "Param1 "; print_char c
  | Param1s s -> print_string "Param1s "; print_string s
  | Range (s, a, b) ->
      print_string ("Range ("^s^", ");
      print_int a; print_string ", "; print_int b; print_string ")"
  | Shouldbe b -> print_string "Shouldbe "; print_bool b;;

(* return a new codgint table obtained by combining an instruction coding table
 * with a mode coding table *)
let merge_dec (i: maplist_element) (m: maplist_element) =
  let ilh, ipca = i and mlh, mpca = m in
  let lh = match mlh, ilh with (* mode before instruction *)
    | LH (im, sm), LH(ii, si) ->
        LH (im@ii, sm^"  "^si) in

  (* merge two bits of two coding tables *)
  let merge_pos_contents pc1 pc2 =
    if pc1 = pc2 then pc1
    else match pc1, pc2 with
      | Range (_, a1, b1), Range (_, a2, b2) ->
          if (a1-b1)>(a2-b2) then pc2 else pc1 (* keep the smallest *)
      | Range _, pc | pc, Range _ -> pc
      | Value _, Value _ -> raise (Invalid_argument "merge_pos_contents")
      | Value _, _ -> pc1
      | _, Value _ -> pc2
      | _ -> raise (Invalid_argument "merge_pos_contents")
  in
  let pca = array_map2 merge_pos_contents mpca ipca in
    lh, pca;;

(* Split the list of programs according to their kind *)
let classify pds =
  let is = ref [] and ms = Array.create 5 [] in
  let rec aux = function
    | (p, d) :: tail -> (
        match p.pkind with
          | Mode i -> ms.(i-1) <- (p,d) :: ms.(i-1)
          | Inst -> is := (p,d) :: !is);
        aux tail
    | [] -> (!is, ms)
  in aux pds;;

(* Patch the W bit for LDRT, LDRBT, STRT, anfd STRBT *)
(* Verbatim from page A5-29:
 * LDRBT, LDRT, STRBT, and STRT only support post-indexed addressing modes.
 * They use a minor modification of the above bit pattern, where bit[21]
 * (the W bit) is 1, not 0 as shown.
 *)
let patch_W (m: prog * maplist_element): prog * maplist_element =
  let i, (lh, pca) = m in
  let pca'= Array.copy pca in
    pca'.(21) <- Value true;
    i, (lh, pca');;

(* Main function *)
let flatten (pcs: prog list) (decs: maplist) : (prog*maplist_element) list =
  let decs' = (* remove encodings *)
    let aux x = add_mode (name x) <> DecEncoding in
      List.filter aux decs
  in
  (* IMPORTANT: normalization of pcs must be done before calling flatten,
   * else List.combine pcs decs' will fail.*)
  let pds = List.combine pcs decs' in
  let is, ms = classify pds in
    (* Flatten one instruction *)
  let flatten_one (i,d: prog * maplist_element) =
    let merge_prog_dec (i, d) (i', d') = (merge_prog i i', merge_dec d d') in
    let is_inst p = match p.pkind with Inst -> true | Mode _ -> false in
      assert (is_inst i);
      match i.pident.iname with
        (* Mode 1: list given in section A3.4 *)
        | "ADC" | "ADD" | "AND" | "BIC" | "EOR" | "ORR" | "MOV" | "MVN"
        | "SUB" | "SBC" | "RSB" | "RSC" | "TST" | "TEQ" | "CMP" | "CMN" ->
            List.map (merge_prog_dec (i,d)) ms.(0)
              
        (* Verbatim from section A5.2:
         * All nine of the following options are available for LDR, LDRB,
         * STR and STRB. For LDRBT, LDRT, STRBT and STRBT, only the
         * post-indexed options (the last three in the list) are available.
         * For the PLD instruction described in PLD on page A4-90, only the
         * offset options (the first three in the list) are available.
         *)
        | "LDR" | "LDRB" | "STR" | "STRB" ->
            List.map (merge_prog_dec (i,d)) ms.(1)
        | "LDRT" | "LDRBT" | "STRT" | "STRBT" ->
            let aux (m,_) = match m.pref with
              | "A5.2.8" | "A5.2.9" | "A5.2.10" -> true
              | _ -> false
            in let ms = List.filter aux ms.(1)
            in let ms' = List.map patch_W ms
            in List.map (merge_prog_dec (i,d)) ms'
        | "PLD" ->
            let aux (m,_) = match m.pref with
              | "A5.2.2" | "A5.2.3" | "A5.2.4" -> true
              | _ -> false
            in List.map (merge_prog_dec (i,d)) (List.filter aux ms.(1))

        (* Mode 3: cf section A5.3 *)
        | "LDRH" | "LDRSH" | "STRH" | "LDRSB" | "LDRD" | "STRD" ->
            List.map (merge_prog_dec (i,d)) ms.(2)

        (* Mode 4: cf section A5.4 *)
        | "LDM" | "STM" ->
            List.map (merge_prog_dec (i,d)) ms.(3)

        (* Mode 5: cf section A5.5 *)
        | "LDC" | "STC" ->
            List.map (merge_prog_dec (i,d)) ms.(4)
              
        (* other instrucitons *)
        | _ -> [(i,d)]
  in List.flatten (List.map flatten_one is);;
