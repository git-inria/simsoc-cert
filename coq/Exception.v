(**
SimSoC-Cert, a Coq library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Exception handling. Step functions are taken from the generated file
arm6/arm6exn.v. *)

Require Import Config List ZArith Bitvec Arm SCC State Semantics Util String.

Module InstSem (Import C : CONFIG).

(* A2.6.2 Reset *)
Definition Reset_step (s0 : state) : result :=
  block (
    set_reg_mode (exn svc) LR (repr 0) ::
    let SPSR_svc := repr 0 in
    set_cpsr (set_bits 4 0 (repr (Zpos 1~0~0~1~1)) (cpsr s0)) ::
    set_cpsr (set_bit 5 (repr 0) (cpsr s0)) ::
    set_cpsr (set_bit 6 (repr 1) (cpsr s0)) ::
    set_cpsr (set_bit 7 (repr 1) (cpsr s0)) ::
    set_cpsr (set_bit 8 (repr 1) (cpsr s0)) ::
    set_cpsr (set_bit 9 ((CP15_reg1 s0)[EEbit]) (cpsr s0)) ::
    if_then_else C.high_vectors_configured
      (set_reg PC (repr (Zpos 4294901760)))
      (set_reg PC (repr (Z0))) ::
    nil) true s0.

(* A2.6.3 UndIns *)
Definition UndIns_step (s0 : state) : result :=
  block (
    set_reg_mode (exn und) LR (address_of_next_instruction s0) ::
    let SPSR_und := cpsr s0 in
    set_cpsr (set_bits 4 0 (repr (Zpos 1~1~0~1~1)) (cpsr s0)) ::
    set_cpsr (set_bit 5 (repr 0) (cpsr s0)) ::
    set_cpsr (set_bit 7 (repr 1) (cpsr s0)) ::
    set_cpsr (set_bit 9 ((CP15_reg1 s0)[EEbit]) (cpsr s0)) ::
    if_then_else C.high_vectors_configured
      (set_reg PC (repr (Zpos 4294901764)))
      (set_reg PC (repr (Zpos 4))) ::
    nil) true s0.

(* A2.6.4 SoftInt *)
Definition SoftInt_step (s0 : state) : result :=
  block (
    set_reg_mode (exn svc) LR (address_of_next_instruction s0) ::
    let SPSR_svc := cpsr s0 in
    set_cpsr (set_bits 4 0 (repr (Zpos 1~0~0~1~1)) (cpsr s0)) ::
    set_cpsr (set_bit 5 (repr 0) (cpsr s0)) ::
    set_cpsr (set_bit 7 (repr 1) (cpsr s0)) ::
    set_cpsr (set_bit 9 ((CP15_reg1 s0)[EEbit]) (cpsr s0)) ::
    if_then_else C.high_vectors_configured
      (set_reg PC (repr (Zpos 4294901768)))
      (set_reg PC (repr (Zpos 8))) ::
    nil) true s0.

(* A2.6.5 PFAbort *)
Definition PFAbort_step (s0 : state) : result :=
  block (
    set_reg_mode (exn abt) LR (add (address_of_current_instruction s0) (repr 4)) ::
    let SPSR_abt := cpsr s0 in
    set_cpsr (set_bits 4 0 (repr (Zpos 1~0~1~1~1)) (cpsr s0)) ::
    set_cpsr (set_bit 5 (repr 0) (cpsr s0)) ::
    set_cpsr (set_bit 7 (repr 1) (cpsr s0)) ::
    set_cpsr (set_bit 8 (repr 1) (cpsr s0)) ::
    set_cpsr (set_bit 9 ((CP15_reg1 s0)[EEbit]) (cpsr s0)) ::
    if_then_else C.high_vectors_configured
      (set_reg PC (repr (Zpos 4294901772)))
      (set_reg PC (repr (Zpos 12))) ::
    nil) true s0.

(* A2.6.6 DataAbort *)
Definition DataAbort_step (s0 : state) : result :=
  block (
    set_reg_mode (exn abt) LR (add (address_of_current_instruction s0) (repr 8)) ::
    let SPSR_abt := cpsr s0 in
    set_cpsr (set_bits 4 0 (repr (Zpos 1~0~1~1~1)) (cpsr s0)) ::
    set_cpsr (set_bit 5 (repr 0) (cpsr s0)) ::
    set_cpsr (set_bit 7 (repr 1) (cpsr s0)) ::
    set_cpsr (set_bit 8 (repr 1) (cpsr s0)) ::
    set_cpsr (set_bit 9 ((CP15_reg1 s0)[EEbit]) (cpsr s0)) ::
    if_then_else C.high_vectors_configured
      (set_reg PC (repr (Zpos 4294901776)))
      (set_reg PC (repr (Zpos 16))) ::
    nil) true s0.

(* A2.6.8 IRQ *)
Definition IRQ_step (s0 : state) : result :=
  block (
    set_reg_mode (exn irq) LR (add (address_of_next_instruction s0) (repr 4)) ::
    let SPSR_irq := cpsr s0 in
    set_cpsr (set_bits 4 0 (repr (Zpos 1~0~0~1~0)) (cpsr s0)) ::
    set_cpsr (set_bit 5 (repr 0) (cpsr s0)) ::
    set_cpsr (set_bit 7 (repr 1) (cpsr s0)) ::
    set_cpsr (set_bit 8 (repr 1) (cpsr s0)) ::
    set_cpsr (set_bit 9 ((CP15_reg1 s0)[EEbit]) (cpsr s0)) ::
    if_then_else (zeq ((CP15_reg1 s0)[VEbit]) 0)
      (if_then_else C.high_vectors_configured
        (set_reg PC (repr (Zpos 4294901784)))
        (set_reg PC (repr (Zpos 24))))
      (set_reg PC (VE_IRQ_address)) ::
    nil) true s0.

(* A2.6.9 FIQ *)
Definition FIQ_step (s0 : state) : result :=
  block (
    set_reg_mode (exn fiq) LR (add (address_of_next_instruction s0) (repr 4)) ::
    let SPSR_fiq := cpsr s0 in
    set_cpsr (set_bits 4 0 (repr (Zpos 1~0~0~0~1)) (cpsr s0)) ::
    set_cpsr (set_bit 5 (repr 0) (cpsr s0)) ::
    set_cpsr (set_bit 6 (repr 1) (cpsr s0)) ::
    set_cpsr (set_bit 7 (repr 1) (cpsr s0)) ::
    set_cpsr (set_bit 8 (repr 1) (cpsr s0)) ::
    set_cpsr (set_bit 9 ((CP15_reg1 s0)[EEbit]) (cpsr s0)) ::
    if_then_else (zeq ((CP15_reg1 s0)[VEbit]) 0)
      (if_then_else C.high_vectors_configured
        (set_reg PC (repr (Zpos 4294901788)))
        (set_reg PC (repr (Zpos 28))))
      (set_reg PC (VE_FIQ_address)) ::
    nil) true s0.

Definition step (s : state) : result :=
  match exns s with
    | nil => Ok false s
    | e :: _ =>
      match e with
        | Reset => Reset_step s
        | UndIns => UndIns_step s
        | SoftInt => SoftInt_step s
        | PFAbort => PFAbort_step s
        | DataAbort => DataAbort_step s
        | ImpAbort => todo "Imprecise data abort" false s
        | IRQ => IRQ_step s
        | FIQ => FIQ_step s
      end
  end.

End InstSem.
