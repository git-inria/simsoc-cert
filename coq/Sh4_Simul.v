(**
SimSoC-Cert, a Coq library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Instruction decoding and execution cycle.
*)

Set Implicit Arguments.

Require Import Bitvec Sh4 Sh4_Semantics Sh4_State Message.

(****************************************************************************)
(** decoding result type *)
(****************************************************************************)

Section decoder_result.

 Variable inst : Type.

 Inductive decoder_result : Type :=
 | DecInst : inst -> decoder_result
 | DecUnpredictable : decoder_result
 | DecError : message -> decoder_result
 | DecUndefined_with_num : nat -> decoder_result.

Notation DecUndefined := (DecUndefined_with_num 0).

End decoder_result.

Definition decode_cond (w : word) (inst : Type) (g : opcode -> inst) :
  decoder_result inst :=
  match condition w with
    | Some oc => DecInst (g oc)
    | None => @DecUndefined_with_num inst 1
  end.

Definition decode_cond_mode (mode : Type) (f : word -> decoder_result mode)
  (w : word) (inst : Type) (g : mode -> opcode -> inst) :
  decoder_result inst :=
  match condition w with
    | Some oc =>
      match f w with
        | DecInst i => DecInst (g i oc)
        | DecError m => @DecError inst m
        | DecUnpredictable => @DecUnpredictable inst
        | DecUndefined => @DecUndefined_with_num inst 2
      end
    | None => @DecUndefined_with_num inst 3
  end.

Definition decode_mode (mode : Type) (f : word -> decoder_result mode)
  (w : word) (inst : Type) (g : mode -> inst) :
  decoder_result inst :=
  match f w with
    | DecInst i => DecInst (g i)
    | DecError m => @DecError inst m
    | DecUnpredictable => @DecUnpredictable inst
    | DecUndefined => @DecUndefined_with_num inst 2
  end.

(****************************************************************************)
(** types and functions necessary for building a simulator *)
(****************************************************************************)

Module Type INST.
  Variable inst : Type.
  Variable step : state -> inst -> result.
  Variable decode : word -> decoder_result inst.
  Variable handle_exception : state -> result.
End INST.

(****************************************************************************)
(** functor building a simulator *)
(****************************************************************************)

(* b true means that the last instruction executed was not a jump *)
(* Because the PC register contains the address of the current instruction
 * plus 8 (cf A2.4.3), we add 8 to the PC if a jump occured (b false) *)
(* The implementation assumes that the processor is in ARM mode *)
Definition incr_PC_ARM (b: bool) (s : state) : state :=
  set_reg s PC (add (reg_content s PC) (repr (if b then 4 else 8))).

Inductive simul_result : Type :=
| SimOk : state -> simul_result
| SimKo : state (* state before the current instruction *)
  -> message (* error message *) -> simul_result.

Module Make (Import I : INST).

  Definition handle_exception (s : state) : simul_result :=
    match handle_exception s with
      | Ok _ _ s' => SimOk s'
      | Ko m | Todo m => SimKo s m
    end.

  Definition next (s : state) : simul_result :=
    match inst_set (cpsr s) with
      | None => SimKo s InvalidInstructionSet
      | Some Jazelle => SimKo s JazelleInstructionSetNotImplemented
      | Some Thumb => SimKo s ThumbInstructionSetNotImplemented
      | Some ARM =>
        let a := address_of_current_instruction s in
        let w := read s a Word in
          match decode w with
            | DecError m => SimKo s m
            | DecUnpredictable => SimKo s DecodingReturnsUnpredictable
            | DecUndefined_with_num fake => SimKo s ComplexSemantics (*handle_exception (add_exn s UndIns)*)
            | DecInst i =>
              match step s i with
                | Ok _ b s' => handle_exception (incr_PC_ARM b s')
                | Ko m | Todo m => SimKo s m
              end
          end
    end.

  Fixpoint simul (s : state) (n : nat) : nat * simul_result :=
    match n with
      | 0%nat => (n, SimOk s)
      | S n' =>
        match next s with
          | SimOk s' => simul s' n'
          | r => (n, r)
        end
    end.

End Make.
