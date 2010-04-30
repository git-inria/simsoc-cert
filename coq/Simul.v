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

Section decoder_result.

 Variable inst : Type.

 Inductive decoder_result : Type :=
 | DecUndefined : decoder_result
 | DecUnpredictable : decoder_result
 | DecInst : inst -> decoder_result.

End decoder_result.

Module Type INST.
  Variable inst : Type.
  Variable step : state -> inst -> result.
  Variable decode : word -> decoder_result inst.
  Variable handle_exception : state -> state.
End INST.

Definition incr_PC (s : state) : state :=
  set_reg s PC (address_of_next_instruction s).

Inductive simul_result : Type :=
| SimOk : state -> simul_result
| SimKo : state -> string -> simul_result.

Module Make (Import I : INST).

  Definition next (s : state) : simul_result :=
    match proc_mode_of_word (cpsr s) with
      | None => SimKo s "invalid processor mode"
      | Some m =>
        match inst_set (cpsr s) with
          | None => SimKo s "invalid instruction set"
          | Some Thumb => SimKo s "Thumb instruction set not implemented"
          | Some Jazelle => SimKo s "Jazelle instruction set not implemented"
          | Some ARM =>
            let w := read s (address_of_word (reg_content s PC)) Word in
              match decode w with
                | DecUnpredictable => SimKo s "decoding is unpredictable"
                | DecUndefined => SimOk (add_exn s UndIns)
                | DecInst i =>
                  match step s i with
                    | Ok b s' =>
                      SimOk (handle_exception (if b then incr_PC s' else s'))
                    | Ko m => SimKo s m
                    | Todo m => SimKo s m
                  end
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
