(**
SimSoC-Cert, a Coq library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the ARM architecture version 6 following the:

ARM Architecture Reference Manual, Issue I, July 2005.

Page numbers refer to ARMv6.pdf.

Instruction decoding and execution cycle.
*)

Set Implicit Arguments.

Require Import State.
Require Import Decode.
Require Import Instructions.
Require Import Semantics.
Require Import Shift.
Require Import Bitvec.

Definition next (s : state) : option state :=
  match mode (cpsr s) with
    | Some m =>
      let a := reg_content s m PC in
      let w := (*FIXME*) mem s (mk_bitvec 30 (bits 2 31 a)) in
        match decode w with
          | Some i =>
            match i with
              | ADC Sbit Rd Rn so =>
                let (v, _) := shifter_operand_value_and_carry s m w so in
                  Adc Sbit Rd Rn v s m
              | ADD Sbit Rd Rn so =>
                let (v, _) := shifter_operand_value_and_carry s m w so in
                  Add Sbit Rd Rn v s m
              | AND Sbit Rd Rn so =>
                let (v, c) := shifter_operand_value_and_carry s m w so in
                  And Sbit Rd Rn v c s m
              | BL L w => Some s (*FIXME*)
            end
          | _ => None
        end
    | None => None
  end.
