(**
SimSoC-Cert, a Coq library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the SH4 architecture following the:

SH-4, Software Manual, Renesas 32-Bit RISC, Rev.6.00 2006.09

Page numbers refer to Renesas_SH4_2006.pdf.

*)

Set Implicit Arguments.

Require Import Coqlib Util Bitvec Sh4 Integers Sh4_State Semantics Message.

Module Semantics.
  Module _Sh4 <: PROC.
    Definition exception := exception.
    Definition instruction_set := instruction_set.
    Definition UndIns := UndIns.
    Definition PC := PC.
    Definition inst_set := inst_set.
  End _Sh4.

  Module _Sh4_State <: STATE _Sh4.
    Definition state := state.
    Definition set_cpsr := set_cpsr.
    Definition set_cpsr_bit := set_cpsr_bit.
    Definition set_reg := set_reg.
    Definition reg_content := reg_content.
    Definition cpsr := cpsr.
    Definition add_exn := add_exn.
    Definition read := read.
    Definition address_of_current_instruction := address_of_current_instruction.
  End _Sh4_State.

  Module Export S := Semantics.Make _Sh4 _Sh4_State. (* COQFIX "The kernel does not recognize yet that a parameter can be instantiated by an inductive type." *)

  Definition Delay_Slot : word -> semfun unit := fun _ => todo ComplexSemantics.
  Definition if_is_dirty_block_then_write_back : word -> semfun unit := fun _ => todo ComplexSemantics.
  Definition if_is_write_back_memory_and_look_up_in_operand_cache_eq_miss_then_allocate_operand_cache_block : word -> semfun unit := fun _ => todo ComplexSemantics.
  Definition invalidate_operand_cache_block : word -> semfun unit := fun _ => todo ComplexSemantics.
  Definition Read_Byte : word -> semfun word := fun _ => todo ComplexSemantics.
  Definition Read_Word : word -> semfun word := fun _ => todo ComplexSemantics.
  Definition Read_Long : word -> semfun word := fun _ => todo ComplexSemantics.
  Definition Sleep_standby : semfun unit := todo ComplexSemantics.
  Definition Write_Byte : word -> word -> semfun unit := fun _ _ => todo ComplexSemantics.
  Definition Write_Word : word -> word -> semfun unit := fun _ _ => todo ComplexSemantics.
  Definition Write_Long : word -> word -> semfun unit := fun _ _ => todo ComplexSemantics.


  Definition Logical_Shift_Left := shl.
  Definition Logical_Shift_Right := shru.

  Definition FPSCR_MASK := repr 4194303. (* FIXME write 0x003FFFFF instead *)
  Definition H_00000100 := repr 256. (* FIXME write 0x00000100 instead *)

  Definition succ := add (repr 1).
  Definition pred x := sub x (repr 1).
  Definition opp := sub (repr 0).

  Definition incr_PC lbs' := 
    let s := st lbs' in
    ok_semstate tt (loc lbs') (bo lbs') (_Sh4_State.set_reg s PC (add (reg_content s PC) (repr (if (bo lbs') then 4 else 8)))).
End Semantics.

Module Decoder.
  Definition next {A B} (_: A -> B) (f_ok : B) (_ : instruction_set) := f_ok.
End Decoder.