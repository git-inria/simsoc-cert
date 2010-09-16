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
let merge_prog (i: prog) (m:prog) =
  {pref = i.pref^", "^m.pref;
   pkind = Inst;
   pident = merge_ident i.pident m.pident;
   pidents = i.pidents @ m.pidents;
   pinst = merge_inst i.pinst m.pinst};;

(* Split the list of programs according to their kind *)
let classify ps =
  let is = ref [] and ms = Array.create 5 [] in
  let rec aux = function
    | p :: tail -> (
        match p.pkind with
          | Mode i -> ms.(i-1) <- p::ms.(i-1)
          | Inst -> is := p::!is);
        aux tail
    | [] -> (!is, ms)
  in aux ps;;

(* Main function *)
let flatten ps =
  let is, ms = classify ps in
    (* Flatten one instruction *)
  let flatten_one (i: prog) =
    let is_inst p = match p.pkind with Inst -> true | Mode _ -> false in
      assert (is_inst i);
      match i.pident.iname with
        (* Mode 1: list given in section A3.4 *)
        | "ADC" | "ADD" | "AND" | "BIC" | "EOR" | "ORR" | "MOV" | "MVN"
        | "SUB" | "SBC" | "RSB" | "RSC" | "TST" | "TEQ" | "CMP" | "CMN" ->
            List.map (merge_prog i) ms.(0)
              
        (* Verbatim from section A5.2:
         * All nine of the following options are available for LDR, LDRB,
         * STR and STRB. For LDRBT, LDRT, STRBT and STRBT, only the
         * post-indexed options (the last three in the list) are available.
         * For the PLD instruction described in PLD on page A4-90, only the
         * offset options (the first three in the list) are available.
         *)
        | "LDR" | "LDRB" | "STR" | "STRB" ->
            List.map (merge_prog i) ms.(1)
        | "LDRT" | "LDRBT" | "STRT" | "STRBT" ->
            let aux m = match m.pref with
              | "A5.2.8" | "A5.2.9" | "A5.2.10" -> true
              | _ -> false
            in List.map (merge_prog i) (List.filter aux ms.(1))
        | "PLD" ->
            let aux m = match m.pref with
              | "A5.2.2" | "A5.2.3" | "A5.2.4" -> true
              | _ -> false
            in List.map (merge_prog i) (List.filter aux ms.(1))

        (* Mode 3: cf section A5.3 *)
        | "LDRH" | "LDRSH" | "STRH" | "LDRSB" | "LDRD" | "STRD" ->
            List.map (merge_prog i) ms.(2)

        (* Mode 4: cf section A5.4 *)
        | "LDM" | "STM" ->
            List.map (merge_prog i) ms.(3)

        (* Mode 5: cf section A5.5 *)
        | "LDC" | "STC" ->
            List.map (merge_prog i) ms.(4)
              
        (* other instrucitons *)
        | _ -> [i]
  in List.flatten (List.map flatten_one is);;
