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

(*REMOVE: to be automatically generated

Definition execute (w : word) (i : instruction)
  (s : state) : result :=
  match i with
    | ADC cond Sbit Rd Rn so =>
      let (v, _) := shifter_operand_value_and_carry s w so in
        Adc cond Sbit Rd Rn v s
    | ADD cond Sbit Rd Rn so =>
      let (v, _) := shifter_operand_value_and_carry s w so in
        Add cond Sbit Rd Rn v s
    | AND cond Sbit Rd Rn so =>
      let (v, c) := shifter_operand_value_and_carry s w so in
        And cond Sbit Rd Rn v s
    | BL cond L w => Bl cond L w s
  end.
*)

Definition incr_PC (s : state) : option state :=
  Some (update_reg PC (next_inst_address s) s).

Definition next (s : state) (m : processor_mode) : option state :=
  match mode (cpsr s) with
    | None => None
    | Some (m) =>
      match inst_set (cpsr s) with
        | None => None
        | Some is =>
          match is with
            | ARM =>
              let a := reg_content s PC in
              let w := mem s (address_of_word a) in (*FIXME?*)
              let r :=
                match decode w with
                  | Unpredictable => None
                  | Undefined => Some (add_exn UndIns s)
                  | Inst i =>
                    match execute w i s with
                      | None => None
                      | Some (b, s') => if b then incr_PC s' else Some s'
                    end
                end
              in match r with
                   | None => None
                   | Some s => handle_exception s
                 end
            | Thumb => None
            | Jazelle => None
          end
      end
  end.
