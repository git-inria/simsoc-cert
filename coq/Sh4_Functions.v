(**
SimSoC-Cert, a Coq library on processor architectures for embedded systems.
See the COPYRIGHTS and LICENSE files.

Formalization of the SH4 architecture following the:

SH-4, Software Manual, Renesas 32-Bit RISC, Rev.6.00 2006.09

Page numbers refer to Renesas_SH4_2006.pdf.

Functions used in the pseudocode.
*)

Set Implicit Arguments.

Require Import Coqlib Util Bitvec Sh4 Integers.


Parameter Sleep_standby : unit -> unit.
Parameter allocate_operand_cache_block : (* 6 *) word -> unit -> unit.
Parameter invalidate_operand_cache_block : (* 6 *) word -> unit -> unit.
Parameter is_dirty_block : (* 6 *) word -> (* 10 *) bool.
Parameter is_write_back_memory_and_look_up_in_operand_cache_eq_miss : (* 6 *) word -> (* 10 *) bool.
Parameter write_back : (* 6 *) word -> unit -> unit.
Parameter Read_Byte : (* 6 *) word -> (* 8 *) word.
Parameter Read_Word : (* 6 *) word -> (* 9 *) word.
Parameter Read_Long : (* 6 *) word -> (* 6 *) word.
Parameter Write_Byte : (* 6 *) word -> (* 6 *) word -> unit -> unit.
Parameter Write_Word : (* 6 *) word -> (* 6 *) word -> unit -> unit.
Parameter Write_Long : (* 6 *) word -> (* 6 *) word -> unit -> unit.
Parameter Delay_Slot : (* 6 *) word -> unit -> unit.



Definition Logical_Shift_Left := shl.
Definition Logical_Shift_Right := shru.