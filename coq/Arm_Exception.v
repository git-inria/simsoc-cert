(**
SimSoC-Cert, a Coq library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Exception handling. Step functions are taken from the generated file
arm6/arm6exn.v. *)

Require Import Arm_Config List ZArith Bitvec Arm Arm_SCC Arm_State Semantics Util Message.

Definition set_cpsr_bits p n v := 
  _get_s0 (fun s0 => set_cpsr (set_bits p n v (cpsr s0))).

Definition set_cpsr_bit n v := 
  _get_s0 (fun s0 => set_cpsr (set_bit n v (cpsr s0))).

Definition set_cpsr_bit_9 := 
  _get_s0 (fun s0 => set_cpsr (set_bit 9 ((CP15_reg1 s0)[EEbit]) (cpsr s0))).

Definition set_reg_mode_adr e f :=
  _get_s0 (fun s0 => set_reg_mode (exn e) LR (f s0)).

Module InstSem (Import C : CONFIG).

(* A2.6.2 Reset *)
Definition Reset_step : semfun unit :=
  block (
    set_reg_mode (exn svc) LR (repr 0) ::
    let SPSR_svc := repr 0 in
    set_cpsr_bits 4 0 (repr (Zpos 1~0~0~1~1)) ::
    set_cpsr_bit 5 (repr 0) ::
    set_cpsr_bit 6 (repr 1) ::
    set_cpsr_bit 7 (repr 1) ::
    set_cpsr_bit 8 (repr 1) ::
    set_cpsr_bit_9 ::
    _get_s0 
      (fun s0 => if_then_else (high_vectors_configured s0)
      (set_reg PC (repr (Zpos 4294901760)))
      (set_reg PC (repr (Z0)))) ::
    nil).

(* A2.6.3 UndIns *)
Definition UndIns_step : semfun unit :=
  block (
    set_reg_mode_adr und address_of_next_instruction ::
    (*let SPSR_und := cpsr s0 in*)
    set_cpsr_bits 4 0 (repr (Zpos 1~1~0~1~1)) ::
    set_cpsr_bit 5 (repr 0) ::
    set_cpsr_bit 7 (repr 1) ::
    set_cpsr_bit_9 ::
    _get_s0
    (fun s0 => if_then_else (high_vectors_configured s0)
      (set_reg PC (repr (Zpos 4294901764)))
      (set_reg PC (repr (Zpos 4)))) ::
    nil).

(* A2.6.4 SoftInt *)
Definition SoftInt_step : semfun unit :=
  block (
    set_reg_mode_adr svc address_of_next_instruction ::
    (*let SPSR_svc := cpsr s0 in*)
    set_cpsr_bits 4 0 (repr (Zpos 1~0~0~1~1)) ::
    set_cpsr_bit 5 (repr 0) ::
    set_cpsr_bit 7 (repr 1) ::
    set_cpsr_bit_9 ::
    _get_s0
    (fun s0 => if_then_else (high_vectors_configured s0)
      (set_reg PC (repr (Zpos 4294901768)))
      (set_reg PC (repr (Zpos 8)))) ::
    nil).

(* A2.6.5 PFAbort *)
Definition PFAbort_step : semfun unit :=
  block (
    set_reg_mode_adr abt (fun s0 => add (address_of_current_instruction s0) (repr 4)) ::
    (*let SPSR_abt := cpsr s0 in*)
    set_cpsr_bits 4 0 (repr (Zpos 1~0~1~1~1)) ::
    set_cpsr_bit 5 (repr 0) ::
    set_cpsr_bit 7 (repr 1) ::
    set_cpsr_bit 8 (repr 1) ::
    set_cpsr_bit_9 ::
    _get_s0
    (fun s0 => if_then_else (high_vectors_configured s0)
      (set_reg PC (repr (Zpos 4294901772)))
      (set_reg PC (repr (Zpos 12)))) ::
    nil).

(* A2.6.6 DataAbort *)
Definition DataAbort_step : semfun unit :=
  block (
    set_reg_mode_adr abt (fun s0 => add (address_of_current_instruction s0) (repr 8)) ::
    (*let SPSR_abt := cpsr s0 in*)
    set_cpsr_bits 4 0 (repr (Zpos 1~0~1~1~1)) ::
    set_cpsr_bit 5 (repr 0) ::
    set_cpsr_bit 7 (repr 1) ::
    set_cpsr_bit 8 (repr 1) ::
    set_cpsr_bit_9 ::
    _get_s0
    (fun s0 => if_then_else (high_vectors_configured s0)
      (set_reg PC (repr (Zpos 4294901776)))
      (set_reg PC (repr (Zpos 16)))) ::
    nil).

(* A2.6.8 IRQ *)
Definition IRQ_step : semfun unit :=
  block (
    set_reg_mode_adr irq (fun s0 => add (address_of_next_instruction s0) (repr 4)) ::
    (*let SPSR_irq := cpsr s0 in*)
    set_cpsr_bits 4 0 (repr (Zpos 1~0~0~1~0)) ::
    set_cpsr_bit 5 (repr 0) ::
    set_cpsr_bit 7 (repr 1) ::
    set_cpsr_bit 8 (repr 1) ::
    set_cpsr_bit_9 ::
    _get_s0
    (fun s0 => if_then_else (zeq ((CP15_reg1 s0)[VEbit]) 0)
      (if_then_else (high_vectors_configured s0)
        (set_reg PC (repr (Zpos 4294901784)))
        (set_reg PC (repr (Zpos 24))))
      (set_reg PC (VE_IRQ_address))) ::
    nil).

(* A2.6.9 FIQ *)
Definition FIQ_step : semfun unit :=
  block (
    set_reg_mode_adr fiq (fun s0 => add (address_of_next_instruction s0) (repr 4)) ::
    (*let SPSR_fiq := cpsr s0 in*)
    set_cpsr_bits 4 0 (repr (Zpos 1~0~0~0~1)) ::
    set_cpsr_bit 5 (repr 0) ::
    set_cpsr_bit 6 (repr 1) ::
    set_cpsr_bit 7 (repr 1) ::
    set_cpsr_bit 8 (repr 1) ::
    set_cpsr_bit_9 ::
    _get_s0
    (fun s0 => if_then_else (zeq ((CP15_reg1 s0)[VEbit]) 0)
      (if_then_else (high_vectors_configured s0)
        (set_reg PC (repr (Zpos 4294901788)))
        (set_reg PC (repr (Zpos 28))))
      (set_reg PC (VE_FIQ_address))) ::
    nil).

Definition step : semfun unit :=
  _get_st (fun s => match exns s with
    | nil => save_s0_false
    | e :: _ =>
      do_then save_s0_true;
      match e with
        | Reset => Reset_step
        | UndIns => UndIns_step
        | SoftInt => SoftInt_step
        | PFAbort => PFAbort_step
        | DataAbort => DataAbort_step
        | ImpAbort => do_then save_s0_false ; todo ImpreciseDataAbort
        | IRQ => IRQ_step
        | FIQ => FIQ_step
      end
  end).

End InstSem.

