(**
SimSoC-Cert, a Coq library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

A2.6 Exceptions (p. 54)
*)

Require Import State.
Require Import ZArith.
Require Import PseudoCode.
Require Import Integers. Import Int.
Require Import Bitvec.

(*Require Import Config.*)

(*Module Exn (C : CONFIG).*)

(****************************************************************************)
(** A2.6 Exceptions (p. 54) *)
(****************************************************************************)

Definition exception_mode (e : exception) : processor_exception_mode :=
  match e with
    | Reset => svc
    | UndIns => und
    | SoftInt => svc
    | ImpAbort => abt
    | PFAbort => abt
    | DataAbort => abt
    | IRQ => irq
    | FIQ => fiq
  end.

Definition exception_vector_address (e : exception) (use_high_vectors : bool)
  : Z :=
  match use_high_vectors with
    | false =>
      match e with
        | Reset =>     (*0x00000000*)  0
        | UndIns =>    (*0x00000004*)  4
        | SoftInt =>   (*0x00000008*)  8
        | PFAbort =>   (*0x0000000C*) 12
        | ImpAbort (*FIXME?*)
        | DataAbort => (*0x00000010*) 16
(*FIXME: depends on VE bit in the system control coprocessor *)
        | IRQ =>       (*0x00000018*) 24
        | FIQ =>       (*0x0000001C*) 28
      end
    | true =>
      match e with
        | Reset =>     (*0xFFFF0000*)
          Zpos 1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0
        | UndIns =>    (*0xFFFF0004*)
          Zpos 1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0~0
        | SoftInt =>   (*0xFFFF0008*)
          Zpos 1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~0~0~0~0~0~0~0~0~0~0~0~1~0~0~0
        | PFAbort =>   (*0xFFFF000C*)
          Zpos 1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~0~0~0~0~0~0~0~0~0~0~0~1~1~0~0
        | ImpAbort (*FIXME?*)
        | DataAbort => (*0xFFFF0010*)
          Zpos 1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~0~0~0~0~0~0~0~0~0~0~1~0~0~0~0
(*FIXME: depends on VE bit in the system control coprocessor *)
        | IRQ =>       (*0xFFFF0018*)
          Zpos 1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~0~0~0~0~0~0~0~0~0~0~1~1~0~0~0
        | FIQ =>       (*0xFFFF001C*)
          Zpos 1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~0~0~0~0~0~0~0~0~0~0~1~1~1~0~0
      end
  end.

Definition interp (s : state) (m : processor_mode) (i : inst)
  : option state :=
  match interp empty s m i with
    | None => None
    | Some (_, s) => Some s
  end.

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

Definition handle_Reset (s : state) (m : processor_mode) : option state :=
  interp s m
  (Seq (Affect (Reg_exn svc w14) All w0) (*FIXME*)
  (Seq (Affect (SPSR svc) All w0) (*FIXME*)
  (Seq (Affect CPSR (Bits 4 0) (W 1~0~0~1~1))
  (Seq (Affect CPSR (Bit 5) w0)
  (Seq (Affect CPSR (Bit 6) w1)
  (Seq (Affect CPSR (Bit 7) w1)
  (Seq (Affect CPSR (Bit 8) w1)
  (Seq (Affect CPSR (Bit 9) w0) (*FIXME*)
  (Affect (Reg w15) All w0))))))))). (*FIXME*)

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

Definition handle_UndIns (s : state) (m : processor_mode) : option state :=
  interp s m
  (Seq (Affect (Reg_exn und w14) All (next_inst_address s m)) (*FIXME?*)
  (Seq (Affect (SPSR svc) All (State CPSR All)) (*FIXME*)
  (Seq (Affect CPSR (Bits 4 0) (W 1~1~0~1~1))
  (Seq (Affect CPSR (Bit 5) w0)
  (Seq (Affect CPSR (Bit 7) w1)
  (Seq (Affect CPSR (Bit 9) w0) (*FIXME*)
  (Affect (Reg w15) All w4))))))). (*FIXME*)

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

Definition handle_SoftInt (s : state) (m : processor_mode) : option state :=
  Some s. (*FIXME*)

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

Definition handle_PFAbort (s : state) (m : processor_mode) : option state :=
  Some s. (*FIXME*)

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

Definition handle_DataAbort (s : state) (m : processor_mode) : option state :=
  Some s. (*FIXME*)

(****************************************************************************)
(* A2.6.7 Imprecise data aborts (p. 61) *)
(****************************************************************************)

Definition handle_ImpAbort (s : state) (m : processor_mode) : option state :=
  Some s. (*FIXME*)

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

Definition handle_IRQ (s : state) (m : processor_mode) : option state :=
  Some s. (*FIXME*)

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

Definition handle_FIQ (s : state) (m : processor_mode) : option state :=
  Some s. (*FIXME*)

(****************************************************************************)
(* Exception priorities (p. 63) *)
(****************************************************************************)

Definition priority (e : exception) : BinInt.Z :=
  match e with
    | Reset => 1 (* highest *)
    | DataAbort => 2
    | FIQ => 3
    | IRQ => 4
    | ImpAbort => 5
    | PFAbort => 6
    | UndIns | SoftInt => 7 (* lowest *)
  end.

Require Import List.
Require Import Coqlib.

(*WARNING: by using this functions, exceptions are always sorted from
the highest priority to the lowest, so that the exception with highest
priority is the first one *)

Fixpoint insert (e : exception) (l : list exception) : list exception :=
  match l with
    | nil => e :: nil
    | e' :: l' => if zlt (priority e) (priority e') then e :: l
      else e' :: insert e l'
  end.

Definition add_exn e s := set_exns s (insert e (exns s)).

Definition handle_exception (s : state) (m : processor_mode) : option state :=
  match exns s with
    | nil => Some s
    | e :: _ =>
      match e with
        | Reset => handle_Reset s m
        | UndIns => handle_UndIns s m
        | SoftInt => handle_SoftInt s m
        | PFAbort => handle_PFAbort s m
        | DataAbort => handle_DataAbort s m
        | ImpAbort => handle_ImpAbort s m
        | IRQ => handle_IRQ s m
        | FIQ => handle_FIQ s m
      end
  end.
