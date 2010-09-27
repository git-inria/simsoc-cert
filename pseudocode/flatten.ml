(**
SimSoC-Cert, a library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Replace each instruction with n mode cases by n instructions with one 1 specific
mode case.
*)

open Printf;;
open Util;;
open Ast;;
open Dec;;
open Codetype;;
open Validity;;

(* type for "flat" programs *)
type fprog = {
  fid: string; (* the identifier used in the generated code *)
  finstr: string; (* the identifier of the base instruction *)
  fmode: string option; (* the identifier of the inlined mode, if any *)
  fref: string; (* chapter(s) in the ARM documentation (e.g. A4.1.20--A5.2.3) *)
  fname: string; (* whole name *)
  finst: inst; (* the pseudo-code *)
  fdec: pos_contents array; (* coding table *)
  fparams: (string * int * int) list; (* the parameters defined in the original 
                                       * coding tables *)
  fvcs: vconstraint list};; (* the validity constraints, from validity.ml *)

(* NB: in general, fparams <> parameters_of fdec, because some parameters disappear
 * when we merge the 2 coding tables *)

(* Example: for "ADCS r0, r1, r2", we have:
 * fid = ADC_M1_Reg
 * finstr = ADC
 * fmode = Some M1_Reg
 * fref = A4.1.2--A5.1.4
 * fname = ADC -- Data processing operands - Register
 * finst =
    begin
      shifter_operand = Rm;
      shifter_carry_out = C Flag;
      if ConditionPassed(cond) then
        begin ... end
    end
 * fdec = pos_contents array of
    |31..28|27...21|20|19..16|15..12|11.....4|3..0|
    | cond |0000101|S |  Rn  |  Rd  |00000000| Rm |
 * fparams = [(cond, 31, 28); (I, 25, 25); (S, 20, 20); (Rn, 19, 16);
              (Rd, 15, 12); (Rm, 3, 0); (shifter_operand, 12, 0)]
 * fvcs = []
 *)

(* Compute an instruction identifier that can be used in Coq or C code *)
let str_ident p =
  let compact s =
    let rec split c s =
      try let l = String.index s c in
        if l = 0 then split c (String.sub s 1 (String.length s - 1))
        else String.sub s 0 l :: split c (String.sub s l (String.length s - l))
      with Not_found -> [s] in
    let abbrev s = match s with
      | "Immediate" | "immediate" -> "Imm"
      | "Register" | "register" -> "Reg"
      | "indexed" -> "Ind"
      | "offset" -> "Off"
      | "Scaled" -> "Sc"
      | "pre" | "post" -> "_"^s
      | "by" | "with" -> ""
      | _ -> String.make 1 (Char.uppercase s.[0]) in
    let ss = split '_' s in
      List.fold_left (fun a b -> a^abbrev b) "" ss in
  let ident b p =
    let i = p.pident in
      match p.pkind with
        | Inst ->
            bprintf b "%s%a%a" i.iname
              (option "" string) i.ivariant (list "" string) i.iparams
        | Mode m ->
            bprintf b "M%d_%s" m (compact i.iname)
  in
  let b = Buffer.create 16 in ident b p; Buffer.contents b;;

(* Get the name of a program as a string *) 
let str_name p =
  let b = Buffer.create 16 in Genpc.name b p; Buffer.contents b;;

(* Sequential composition of two instructions *)
let merge_inst (i: inst) (m: inst) = match m, i with
  | Block l1, Block l2 -> Block (l1@l2)
  | Block l, i -> Block (l@[i])
  | i, Block l -> Block (i::l)
  | i, j -> Block([i; j]);;

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
let merge_dec (ipca: pos_contents array) (mpca: pos_contents array) =
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
  in array_map2 merge_pos_contents mpca ipca;;

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

(* For SRS and RFE, "register_list" is a constant *)
let patch_SRS_RFE (p: prog) =
  let o = Fun ("Number_Of_Set_Bits_In", [Var "register_list"])
  and n = Num "2"
  in let i = Norm.replace_exp o n p.pinst
  in {p with pinst = i};;

(* SRS does take "Rn" for its arguments
 * verbatim from page A4-174:
 * The base register, Rn, is the banked version of R13 for the mode specified
 * by <mode>, rather than the current mode.
 *)
let patch_SRS (p: prog) =
  let o = Reg (Var "n", None)
  and n = Fun ("reg_m", [Num "13"; Var "mode"])
    (* FIXME: "n" should be "Reg (Num "13", Some (Var "mode"))", but it 
    * is not allowed by the Ast.exp type *)
  in let i = Norm.replace_exp o n p.pinst
  in {p with pinst = i};;

(* get the list of parameters *)
let parameters_of (pca: pos_contents array) : (string * int * int) list =
  let rename s =
    if s.[0] = 'R'
    then String.sub s 1 (String.length s -1)
    else match s with
      | "8_bit_immediate" -> "immed_8" (* renamed in preproc_pseudo.sh *)
      | "sh" -> "shift" (* work-around for specification erratum *)
      | "ImmedL" -> "immedL" (* work-around for specification erratum *)
      | _ -> s
  in
  let aux (n, l) pc = match pc with
    | Codetype.Param1 c -> (n+1, (String.make 1 c, n, n) :: l)
    | Codetype.Param1s s-> (n+1, (rename s, n, n) :: l)
    | Codetype.Range (s, size, _) ->
        let s' = rename s in
        let e = s', n+size-1, n in
          (n+1, (
             match l with (* avoid duplicates *)
               | (x, _, _) :: _ -> if x = s' then l else e :: l
               | [] -> [e]
           ))
    | _ -> (n+1, l)
  in
  let _, ps = Array.fold_left aux (0, []) pca in ps;;

(* merge two lists of parameter, and remove duplicates *)
let rec merge_plist a b =
  let cmp ((a:string),_,_) ((b:string),_,_) = compare a b in
  let l = List.merge cmp (List.sort cmp b) (List.sort cmp a) in
  let rec uniq ((a:string),_,_) = function
    | (b,_,_) as hd :: tl -> if a = b then uniq hd tl else hd :: (uniq hd tl)
    | [] -> []
  in match l with
    | hd :: tl -> hd :: (uniq hd tl) 
    | [] -> [];;
(* FIXME: there are 2 defintions for the register_list parameter of LDM(3)
 * currently, we keep only the definition from the addressing mode *)

(* Main function *)
let flatten (pcs: prog list) (decs: maplist) : fprog list =
  let decs' = (* remove encodings *)
    let aux x = add_mode (name x) <> DecEncoding in
      List.filter aux decs
  in
  (* IMPORTANT: normalization of pcs must be done before calling flatten,
   * else List.combine pcs decs' will fail.*)
  let pds = List.combine pcs decs' in
  let is, ms = classify pds in
    (* Flatten one instruction *)
  let flatten_one (i,(_,d): prog * maplist_element) =
    
    let merge_progs (i, d) (i', (_, d')) =
      let idi = str_ident i and idm = str_ident i' in
      let id = idi ^ "_" ^ idm in
      let ref' = i.pref ^ "--" ^ i'.pref in
      let name = str_name i  ^ " -- " ^ str_name i' in
      let inst = merge_inst i.pinst i'.pinst in
      let dec = merge_dec d d' in
      let params = merge_plist (parameters_of d) (parameters_of d') in
      let vcs = get_constraints idi @ get_constraints idm in
      {fid = id; finstr = idi; fmode = Some idm; fref = ref'; fname = name;
       finst = inst; fdec = dec; fparams = params; fvcs = vcs}
    in
    let is_inst p = match p.pkind with Inst -> true | Mode _ -> false in
      assert (is_inst i);
      match i.pident.iname with
        (* Mode 1: list given in section A3.4 *)
        | "ADC" | "ADD" | "AND" | "BIC" | "EOR" | "ORR" | "MOV" | "MVN"
        | "SUB" | "SBC" | "RSB" | "RSC" | "TST" | "TEQ" | "CMP" | "CMN" ->
            List.map (merge_progs (i,d)) ms.(0)
              
        (* Verbatim from section A5.2:
         * All nine of the following options are available for LDR, LDRB,
         * STR and STRB. For LDRBT, LDRT, STRBT and STRBT, only the
         * post-indexed options (the last three in the list) are available.
         * For the PLD instruction described in PLD on page A4-90, only the
         * offset options (the first three in the list) are available.
         *)
        | "LDR" | "LDRB" | "STR" | "STRB" ->
            List.map (merge_progs (i,d)) ms.(1)
        | "LDRT" | "LDRBT" | "STRT" | "STRBT" ->
            let aux (m,_) = match m.pref with
              | "A5.2.8" | "A5.2.9" | "A5.2.10" -> true
              | _ -> false
            in let ms = List.filter aux ms.(1)
            in let ms' = List.map patch_W ms
            in List.map (merge_progs (i,d)) ms'
        | "PLD" ->
            let aux (m,_) = match m.pref with
              | "A5.2.2" | "A5.2.3" | "A5.2.4" -> true
              | _ -> false
            in List.map (merge_progs (i,d)) (List.filter aux ms.(1))

        (* Mode 3: cf section A5.3 *)
        | "LDRH" | "LDRSH" | "STRH" | "LDRSB" | "LDRD" | "STRD" ->
            List.map (merge_progs (i,d)) ms.(2)

        (* Mode 4: cf section A5.4 *)
        | "LDM" | "STM" ->
            List.map (merge_progs (i,d)) ms.(3)
        | "RFE" ->
            let aux (i, d) = patch_SRS_RFE i, d in
            List.map (merge_progs (i, d)) (List.map aux ms.(3))
        | "SRS" ->
            let aux (i, d) = patch_SRS (patch_SRS_RFE i), d in
            List.map (merge_progs (i, d)) (List.map aux ms.(3))

        (* Mode 5: cf section A5.5 *)
        | "LDC" | "STC" ->
            List.map (merge_progs (i,d)) ms.(4)
              
        (* other instrucitons *)
        | _ ->
            let id = str_ident i in
              [{fid = id; finstr = id; fmode = None; fref = i.pref;
                fname = str_name i; finst = i.pinst;
                fdec = d; fparams = parameters_of d; fvcs = get_constraints id}]
  in List.flatten (List.map flatten_one is);;
