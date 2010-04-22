(**
SimSoC-Cert, a Coq library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Exception handling.
*)

Require Import List State Arm.

(****************************************************************************)
(* A2.6.2 Reset (p. 56) *)
(****************************************************************************)

(* <<
R14_svc = UNPREDICTABLE value
SPSR_svc = UNPREDICTABLE value
CPSR[4:0] = 0b10011 /* Enter Supervisor mode */
CPSR[5] = 0 /* Execute in ARM state */
CPSR[6] = 1 /* Disable fast interrupts */
CPSR[7] = 1 /* Disable normal interrupts */
CPSR[8] = 1 /* Disable Imprecise Aborts (v6 only) */
CPSR[9] = CP15_reg1_EEbit /* Endianness on exception entry */
if high vectors configured then
  PC = 0xFFFF0000
else
  PC = 0x00000000
>>*)

Definition handle_Reset (s : state) : option state := Some s.

(*Definition handle_Reset (s : state) (m : processor_mode) : option state :=
  Some s. (*FIXME*)*)
  (*interp s m
  (Seq (Affect (Reg_exn svc w14) All w0) (*FIXME*)
  (Seq (Affect (SPSR svc) All w0) (*FIXME*)
  (Seq (Affect CPSR (Bits 4 0) (W 1~0~0~1~1))
  (Seq (Affect CPSR (Bit 5) w0)
  (Seq (Affect CPSR (Bit 6) w1)
  (Seq (Affect CPSR (Bit 7) w1)
  (Seq (Affect CPSR (Bit 8) w1)
  (Seq (Affect CPSR (Bit 9) w0) (*FIXME*)
  (Affect (Reg w15) All w0))))))))). (*FIXME*)*)

(****************************************************************************)
(* A2.6.3 Undefined Instruction exception (p. 57) *)
(****************************************************************************)

(* <<
R14_und = address of next instruction after the Undefined instruction
SPSR_und = CPSR
CPSR[4:0] = 0b11011 /* Enter Undefined Instruction mode */
CPSR[5] = 0 /* Execute in ARM state */
/* CPSR[6] is unchanged */
CPSR[7] = 1 /* Disable normal interrupts */
/* CPSR[8] is unchanged */
CPSR[9] = CP15_reg1_EEbit /* Endianness on exception entry */
if high vectors configured then
  PC = 0xFFFF0004
else
  PC = 0x00000004
>>*)

Definition handle_UndIns (s : state) : option state := Some s.

(*Definition handle_UndIns (s : state) (m : processor_mode) : option state :=
  Some s. (*FIXME*)*)
  (*interp s m
  (Seq (Affect (Reg_exn und w14) All (next_inst_address s m)) (*FIXME?*)
  (Seq (Affect (SPSR svc) All (State CPSR All)) (*FIXME*)
  (Seq (Affect CPSR (Bits 4 0) (W 1~1~0~1~1))
  (Seq (Affect CPSR (Bit 5) w0)
  (Seq (Affect CPSR (Bit 7) w1)
  (Seq (Affect CPSR (Bit 9) w0) (*FIXME*)
  (Affect (Reg w15) All w4))))))). (*FIXME*)*)

(****************************************************************************)
(* A2.6.4 Software Interrupt exception (p. 58) *)
(****************************************************************************)

(* <<
R14_svc = address of next instruction after the SWI instruction
SPSR_svc = CPSR
CPSR[4:0] = 0b10011 /* Enter Supervisor mode */
CPSR[5] = 0 /* Execute in ARM state */
/* CPSR[6] is unchanged */
CPSR[7] = 1 /* Disable normal interrupts */
/* CPSR[8] is unchanged */
CPSR[9] = CP15_reg1_EEbit /* Endianness on exception entry */
if high vectors configured then
  PC = 0xFFFF0008
else
  PC = 0x00000008
>>*)

Definition handle_SoftInt (s : state) : option state := Some s.

(*Definition handle_SoftInt (s : state) (m : processor_mode) : option state :=
  Some s. (*FIXME*)*)

(****************************************************************************)
(* A2.6.5 Prefetch Abort (instruction fetch memory abort) (p. 58) *)
(****************************************************************************)

(* <<
R14_abt = address of the aborted instruction + 4
SPSR_abt = CPSR
CPSR[4:0] = 0b10111 /* Enter Abort mode */
CPSR[5] = 0 /* Execute in ARM state */
/* CPSR[6] is unchanged */
CPSR[7] = 1 /* Disable normal interrupts */
CPSR[8] = 1 /* Disable Imprecise Data Aborts (v6 only) */
CPSR[9] = CP15_reg1_EEbit /* Endianness on exception entry */
if high vectors configured then
  PC = 0xFFFF000C
else
  PC = 0x0000000C
>>*)

Definition handle_PFAbort (s : state) : option state := Some s.

(*Definition handle_PFAbort (s : state) (m : processor_mode) : option state :=
  Some s. (*FIXME*)*)

(****************************************************************************)
(* A2.6.6 Data Abort (data access memory abort) (p. 59) *)
(****************************************************************************)

(* <<
R14_abt = address of the aborted instruction + 8
SPSR_abt = CPSR
CPSR[4:0] = 0b10111 /* Enter Abort mode */
CPSR[5] = 0 /* Execute in ARM state */
/* CPSR[6] is unchanged */
CPSR[7] = 1 /* Disable normal interrupts */
CPSR[8] = 1 /* Disable Imprecise Data Aborts (v6 only) */
CPSR[9] = CP15_reg1_EEbit /* Endianness on exception entry */
if high vectors configured then
  PC = 0xFFFF0010
else
  PC = 0x00000010
>>*)

Definition handle_DataAbort (s : state) : option state := Some s.

(*Definition handle_DataAbort (s : state) (m : processor_mode) : option state :=
  Some s. (*FIXME*)*)

(****************************************************************************)
(* A2.6.7 Imprecise data aborts (p. 61) *)
(****************************************************************************)

Definition handle_ImpAbort (s : state) : option state := Some s.

(*Definition handle_ImpAbort (s : state) (m : processor_mode) : option state :=
  Some s. (*FIXME*)*)

(****************************************************************************)
(* A2.6.8 Interrupt request (IRQ) exception (p. 62) *)
(****************************************************************************)

(* <<
R14_irq = address of next instruction to be executed + 4
SPSR_irq = CPSR
CPSR[4:0] = 0b10010 /* Enter IRQ mode */
CPSR[5] = 0 /* Execute in ARM state */
/* CPSR[6] is unchanged */
CPSR[7] = 1 /* Disable normal interrupts */
CPSR[8] = 1 /* Disable Imprecise Data Aborts (v6 only) */
CPSR[9] = CP15_reg1_EEbit /* Endianness on exception entry */
if VE==0 then
  if high vectors configured then
    PC = 0xFFFF0018
  else
    PC = 0x00000018
else
  PC = IMPLEMENTATION DEFINED /* see page A2-26 (p. 64) */
>>*)

Definition handle_IRQ (s : state) : option state := Some s.

(*Definition handle_IRQ (s : state) (m : processor_mode) : option state :=
  Some s. (*FIXME*)*)

(****************************************************************************)
(* A2.6.9 Fast interrupt request (FIQ) exception (p. 62) *)
(****************************************************************************)

(* <<
R14_fiq = address of next instruction to be executed + 4
SPSR_fiq = CPSR
CPSR[4:0] = 0b10001 /* Enter FIQ mode */
CPSR[5] = 0 /* Execute in ARM state */
CPSR[6] = 1 /* Disable fast interrupts */
CPSR[7] = 1 /* Disable normal interrupts */
CPSR[8] = 1 /* Disable Imprecise Data Aborts (v6 only) */
CPSR[9] = CP15_reg1_EEbit /* Endianness on exception entry */
if VE==0 then
  if high vectors configured then
    PC = 0xFFFF001C
  else
    PC = 0x0000001C
else
  PC = IMPLEMENTATION DEFINED /* see page A2-26 (p. 64) */
>>*)

Definition handle_FIQ (s : state) : option state := Some s.

(*Definition handle_FIQ (s : state) (m : processor_mode) : option state :=
  Some s. (*FIXME*)*)

Definition handle_exception (s : state) : option state :=
  match exns s with
    | nil => Some s
    | e :: _ =>
      match e with
        | Reset => handle_Reset s
        | UndIns => handle_UndIns s
        | SoftInt => handle_SoftInt s
        | PFAbort => handle_PFAbort s
        | DataAbort => handle_DataAbort s
        | ImpAbort => handle_ImpAbort s
        | IRQ => handle_IRQ s
        | FIQ => handle_FIQ s
      end
  end.
