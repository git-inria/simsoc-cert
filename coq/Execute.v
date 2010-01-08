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
Require Import Integers. Import Int.
Require Import Coqlib.
Require Import Exception.

Definition execute (m : processor_mode) (w : word) (i : instruction)
  (s : state) : result :=
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
    | BL L w => Bl L w s m
  end.

Definition next (s : state) : option state :=
  match mode (cpsr s) with
    | None => None
    | Some m =>
      match inst_set (cpsr s) with
        | None => None
        | Some is =>
          match is with
            | ARM =>
              let a := reg_content s m PC in
              let w := mem s (address_of_word a) in (*FIXME?*)
              let r :=
                match decode w with
                  | Unpredictable => None
                  | Undefined => Some (add_exn UndIns s)
                  | Inst i =>
                    match execute m w i s with
                      | None => None
                      | Some (b, s') => if b then incr_PC m s' else Some s'
                    end
                end
              in match r with
                   | None => None
                   | Some s => handle_exception s m
                 end
            | Thumb => None
            | Jazelle => None
          end
      end
  end.
