(**
SimSoC-Cert, a Coq library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Instruction decoding and execution cycle.
*)

Set Implicit Arguments.

Require Import Bitvec Arm Semantics State String.

(****************************************************************************)
(** decoding result type *)
(****************************************************************************)

Section decoder_result.

 Variable inst : Type.

 Inductive decoder_result : Type :=
 | DecUndefined : decoder_result
 | DecUnpredictable : decoder_result
 | DecInst : inst -> decoder_result
 | DecError : string -> decoder_result.

End decoder_result.

(*REMOVE:*)
Definition decode_mode (mode : Type) (inst : Type) 
  (f : word -> decoder_result mode) (w : word) (g : mode -> inst) :
  decoder_result inst :=
  match f w with
    | DecInst i => DecInst (g i)
    | DecError m => @DecError inst m
    | DecUndefined => @DecUndefined inst
    | DecUnpredictable => @DecUnpredictable inst
  end.

Definition decode_cond (w : word) (inst : Type) (g :option opcode -> inst) :
  decoder_result inst :=
  match condition w with
    | Some oc => DecInst (g (Some oc))
    | None => @DecUndefined inst
  end.

Definition decode_cond_mode (mode : Type) (f : word -> decoder_result mode)
  (w : word) (inst : Type) (g : mode -> option opcode -> inst) :
  decoder_result inst :=
  match condition w with
    | Some oc =>
      match f w with
        | DecInst i => DecInst (g i (Some oc))
        | DecError m => @DecError inst m
        | DecUndefined => @DecUndefined inst
        | DecUnpredictable => @DecUnpredictable inst
      end
    | None => @DecUndefined inst
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

Definition incr_PC (s : state) : state :=
  set_reg s PC (address_of_next_instruction s).

Inductive simul_result : Type :=
| SimOk : state -> simul_result
| SimKo : state (* state before the current instruction *)
  -> string (* error message *) -> simul_result.

Module Make (Import I : INST).

  Definition handle_exception (s : state) : simul_result :=
    match handle_exception s with
      | Ok _ s' => SimOk s'
      | Ko m | Todo m => SimKo s m
    end.

  Definition next (s : state) : simul_result :=
    match inst_set (cpsr s) with
      | None => SimKo s "invalid instruction set"
      | Some Jazelle => SimKo s "Jazelle instruction set not implemented"
      | Some Thumb => SimKo s "Thumb instruction set not implemented"
      | Some ARM =>
        let w := read s (address_of_word (reg_content s PC)) Word in
          match decode w with
            | DecError m => SimKo s m
            | DecUnpredictable => SimKo s "decoding returns unpredictable"
            | DecUndefined => handle_exception (add_exn s UndIns)
            | DecInst i =>
              match step s i with
                | Ok b s' => handle_exception (if b then incr_PC s' else s')
                | Ko m | Todo m => SimKo s m
              end
          end
    end.

  Fixpoint simul (s : state) (n : nat) : nat * simul_result :=
    match n with
      | 0 => (n, SimOk s)
      | S n' =>
        match next s with
          | SimOk s' => simul s' n'
          | r => (n, r)
        end
    end.

End Make.
