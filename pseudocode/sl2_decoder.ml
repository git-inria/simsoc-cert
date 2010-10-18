(**
SimSoC-Cert, a library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Generate the decoders used by simlight2
*)

open Sl2_patch;;
open Sl2_semantics;; (* for the generation of validity tests *)
open Flatten;;
open Util;;
open Printf;;

(* Each decoder starts with a switch on the following opcode:
 * - ARM: (cond<>15) followed by bits 27 to 20 (9 bits, 512 cases)
 * - Thumb: bits 15 to 11 (5 bits, 32 cases)
 *) 

let binary k i =
  let is_set n w =
    Int32.logand Int32.one (Int32.shift_right_logical w n) <> Int32.zero in
  let n = match k with ARM -> 9 | Thumb -> 5 in
  let s = String.make n '0' in
    for b = 0 to n-1 do
      if is_set b (Int32.of_int i) then (s.[n-b-1] <- '1')
    done; s;;

(** Generation of the decoder *)

module type DecoderConfig = sig
  (* the version, such as "decode_exec" or "decode_store" *)
  val version: string;;
  (* the profile of the main decoder functions *)
  val main_prof: Buffer.t -> fkind -> unit;;
  (* the profile of the specific instruction decoder functions *)
  val instr_prof: Buffer.t -> (fkind * string) -> unit;;
  (* how to call an instruction decoder function *)
  val instr_call: Buffer.t -> string -> unit;;
  (* what we do once the instruction is decoded *)
  val action: Buffer.t -> xprog ->unit;;
  (* what we do when we return from the decoder *)
  val return_action: string;;
end;;

module DecoderGenerator (DC: DecoderConfig) = struct
  (* Generation of a decoder in a separated .c file *)
  (*  * - bn: file basename *)
  (*  * - is: the instructions *)
  let decoder bn (k: fkind) (is: xprog list) =

    let class_count = match k with ARM -> 512 | Thumb -> 32 in
    let classes = Array.create class_count [] in
    let classify p =
      let mask, value = Gencxx.mask_value p.xprog.fdec in 
      let opmask, opcode = match k with
        | Thumb ->
            let aux w = Int32.shift_right_logical w 11 in aux mask, aux value
        | ARM ->
            let aux w =
              let w' = Int32.shift_right_logical (Int32.shift_left w 4) 24 in
                if is_conditional p then w' else Int32.logor w' (Int32.of_int 0x100)
            in aux mask, aux value
      in for i = 0 to class_count -1 do
          if Int32.logand (Int32.of_int i) opmask = opcode
          then classes.(i) <- p :: classes.(i)
          else ()
        done
    in List.iter classify is;

    (* Phase A: check bits fixed by the coding table *)
    let instA b p =
      let (mask, value) = Gencxx.mask_value p.xprog.fdec in
      bprintf b "    if ((bincode&0x%08lx)==0x%08lx && %a) {\n"
        mask value DC.instr_call p.xprog.fid;
      bprintf b "      assert(!found); found = true;\n    }\n"
  in
    (* Phase B: extract parameters and check validity *)
  let instB b p =
    bprintf b "%astatic %a {\n"
      comment p DC.instr_prof (k, p.xprog.fid);
    (* extract parameters *)
    let vc = Validity.vcs_to_exp p.xprog.fvcs 
    and params = p.xprog.fparams in
      bprintf b "%a"
        (list "" (Gencxx.dec_param p.xps vc)) params;
      (* integrate H1 and H2 (see for example thumb ADD (4)) *)
      if List.exists (fun (n,_,_) -> n = "H1") params then (
        let r = if List.exists (fun (n,_,_) -> n = "d") params then "d" else "n"
        in bprintf b "  %s |= H1 << 3;\n" r
      );
      if List.exists (fun (n,_,_) -> n = "H2") params then (
        bprintf b "  m |= H2 << 3;\n"
      );
      (* check validity *)
      (match vc with
         | Some e -> bprintf b "  if (!(%a)) return false;\n" (exp p) e
         | None -> ());
      (* compute the "computed" parameters *)
      let aux (b: Buffer.t) ((n, t): (string * string)) : unit =
        bprintf b "  const %s %s = %s;\n" t n (compute_param n)
      in bprintf b "%a" (list "" aux) p.xcs;
      (* execute the instruction *)
      bprintf b "%a" DC.action p;
      bprintf b "  return true;\n}\n"
  in
  let b = Buffer.create 10000 in
    bprintf b "#include \"%s_c_prelude.h\"\n\n" bn;
    bprintf b "%a\n" (list "\n" instB) is;
    bprintf b "/* the main function, used by the ISS loop */\n";
    bprintf b "%a {\n" DC.main_prof k;
    bprintf b "  bool found = false;\n";
    ( match k with
       | ARM ->
           bprintf b "  const uint32_t c = bincode>>28;\n";
           bprintf b
             "  const uint32_t opcode = (c==15 ? 0x100 : 0) | (bincode<<4)>>24;\n"
       | Thumb ->
           bprintf b "  const uint16_t opcode = bincode>>11;\n"
    );
    bprintf b "  switch (opcode) {\n";
    for i = 0 to class_count - 1 do
      bprintf b "  case %d: /* %s */\n" i (binary k i);
      if i+1=class_count || classes.(i) <> classes.(i+1) then
        bprintf b "%a    break;\n" (list "" instA) classes.(i)
      else ()
    done;
    bprintf b "  }\n";
    bprintf b "  %s\n}\n" DC.return_action;
    bprintf b "\nEND_SIMSOC_NAMESPACE\n";
    let s = if k = ARM then "arm" else "thumb" in
    let outc = open_out (bn^"_"^s^"_"^DC.version^".c") in
      Buffer.output_buffer outc b; close_out outc;;
end;;

module DecExecConfig = struct
  let version = "decode_exec";;
  let main_prof b (k: fkind) =
    let s, n = if k = ARM then "arm", 32 else "thumb", 16 in
      bprintf b
        "bool %s_decode_and_exec(struct SLv6_Processor *proc, uint%d_t bincode)"
        s n;;
  let instr_prof b ((k: fkind), id) =
    bprintf b "bool try_exec_%s(struct SLv6_Processor *proc, uint%d_t bincode)"
      id (if k = ARM then 32 else 16);;
  let instr_call b id = bprintf b "try_exec_%s(proc,bincode)" id;;
  let action b (x: xprog) =
    let aux b (s,_) = bprintf b ",%s" s in
      bprintf b "  slv6_X_%s(proc%a);\n" x.xprog.fid (list "" aux) (x.xkps @ x.xcs);;
  let return_action = "return found;"
end;;
module DecExec = DecoderGenerator(DecExecConfig);;

module DecStoreConfig = struct
  let version = "decode_store";;
  let main_prof b (k: fkind) =
    let s, n = if k = ARM then "arm", 32 else "thumb", 16 in
      bprintf b
        "void %s_decode_and_store(struct SLv6_Instruction *instr, uint%d_t bincode)"
        s n;;
  let instr_prof b ((k: fkind), id) =
    bprintf b "bool try_store_%s(struct SLv6_Instruction *instr, uint%d_t bincode)"
      id (if k = ARM then 32 else 16);;
  let instr_call b id = bprintf b "try_store_%s(instr,bincode)" id;;
  let action b (x: xprog) =
    let store b (n, _) = 
      bprintf b "  instr->args.%s.%s = %s;\n" (union_id x) n n
    in
      if is_conditional x then (
        bprintf b "  if (cond==SLV6_AL)\n";
        bprintf b "    instr->args.g0.id = SLV6_%s_NC_ID;\n" x.xprog.fid;
        bprintf b "  else\n  ");
      bprintf b "  instr->args.g0.id = SLV6_%s_ID;\n" x.xprog.fid;
      bprintf b "%a" (list "" store) (x.xkps @ x.xcs);;
  let return_action = "if (!found) instr->args.g0.id = SLV6_UNPRED_OR_UNDEF_ID;"
end;;
module DecStore = DecoderGenerator(DecStoreConfig);;
