open Bitvec
open Integers
open Message
open Simul
open Arm6inst

let decode_addr_mode1 (w : word) =
 match w28_of_word w with
    (*5.1.13 - Data-processing operands - Rotate right with extend*)
    | word28 0 0 0 _ _ _ _ S_ _ _ _ _ _ _ _ _ 0 0 0 0 0 1 1 0 _ _ _ _ ->
      DecInst (M1_Rotate_right_with_extend (regnum_from_bit n0 w))
    (*5.1.3 - Data-processing operands - Immediate*)
    | word28 0 0 1 _ _ _ _ S_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ->
      DecInst (M1_Immediate (bits n7 n0 w) (bits n11 n8 w))
    (*5.1.4 - Data-processing operands - Register*)
    | word28 0 0 0 _ _ _ _ S_ _ _ _ _ _ _ _ _ 0 0 0 0 0 0 0 0 _ _ _ _ ->
      DecInst (M1_Register (regnum_from_bit n0 w))
    (*5.1.5 - Data-processing operands - Logical shift left by immediate*)
    | word28 0 0 0 _ _ _ _ S_ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 0 0 _ _ _ _ ->
      DecInst (M1_Logical_shift_left_by_immediate (regnum_from_bit n0 w) (bits n11 n7 w))
    (*5.1.6 - Data-processing operands - Logical shift left by register*)
    | word28 0 0 0 _ _ _ _ S_ _ _ _ _ _ _ _ _ _ _ _ _ 0 0 0 1 _ _ _ _ ->
      DecInst (M1_Logical_shift_left_by_register (regnum_from_bit n0 w) (regnum_from_bit n8 w))
    (*5.1.7 - Data-processing operands - Logical shift right by immediate*)
    | word28 0 0 0 _ _ _ _ S_ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 1 0 _ _ _ _ ->
      DecInst (M1_Logical_shift_right_by_immediate (regnum_from_bit n0 w) (bits n11 n7 w))
    (*5.1.8 - Data-processing operands - Logical shift right by register*)
    | word28 0 0 0 _ _ _ _ S_ _ _ _ _ _ _ _ _ _ _ _ _ 0 0 1 1 _ _ _ _ ->
      DecInst (M1_Logical_shift_right_by_register (regnum_from_bit n0 w) (regnum_from_bit n8 w))
    (*5.1.9 - Data-processing operands - Arithmetic shift right by immediate*)
    | word28 0 0 0 _ _ _ _ S_ _ _ _ _ _ _ _ _ _ _ _ _ _ 1 0 0 _ _ _ _ ->
      DecInst (M1_Arithmetic_shift_right_by_immediate (regnum_from_bit n0 w) (bits n11 n7 w))
    (*5.1.10 - Data-processing operands - Arithmetic shift right by register*)
    | word28 0 0 0 _ _ _ _ S_ _ _ _ _ _ _ _ _ _ _ _ _ 0 1 0 1 _ _ _ _ ->
      DecInst (M1_Arithmetic_shift_right_by_register (regnum_from_bit n0 w) (regnum_from_bit n8 w))
    (*5.1.11 - Data-processing operands - Rotate right by immediate*)
    | word28 0 0 0 _ _ _ _ S_ _ _ _ _ _ _ _ _ _ _ _ _ _ 1 1 0 _ _ _ _ ->
      DecInst (M1_Rotate_right_by_immediate (regnum_from_bit n0 w) (bits n11 n7 w))
    (*5.1.12 - Data-processing operands - Rotate right by register*)
    | word28 0 0 0 _ _ _ _ S_ _ _ _ _ _ _ _ _ _ _ _ _ 0 1 1 1 _ _ _ _ ->
      DecInst (M1_Rotate_right_by_register (regnum_from_bit n0 w) (regnum_from_bit n8 w))
    | _ -> DecError mode1 NotAnAddressingMode1
;;

let decode_addr_mode2 (w : word) =
 match w28_of_word w with
    (*5.2.2 - Load and Store Word or Unsigned Byte - Immediate offset*)
    | word28 0 1 0 1 U_ B_ 0 L_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ->
      decode_cond w (fun condition => M2_Immediate_offset U_ (regnum_from_bit n16 w) (bits n11 n0 w))
    (*5.2.3 - Load and Store Word or Unsigned Byte - Register offset*)
    | word28 0 1 1 1 U_ B_ 0 L_ _ _ _ _ _ _ _ _ 0 0 0 0 0 0 0 0 _ _ _ _ ->
      decode_cond w (fun condition => M2_Register_offset U_ (regnum_from_bit n0 w) (regnum_from_bit n16 w))
    (*5.2.4 - Load and Store Word or Unsigned Byte - Scaled register offset*)
    | word28 0 1 1 1 U_ B_ 0 L_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 _ _ _ _ ->
      decode_cond w (fun condition => M2_Scaled_register_offset U_ (regnum_from_bit n0 w) (regnum_from_bit n16 w) (bits n6 n5 w) (bits n11 n7 w))
    (*5.2.5 - Load and Store Word or Unsigned Byte - Immediate pre-indexed*)
    | word28 0 1 0 1 U_ B_ 1 L_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ->
      decode_cond w (fun condition => M2_Immediate_pre_indexed U_ condition (regnum_from_bit n16 w) (bits n11 n0 w))
    (*5.2.6 - Load and Store Word or Unsigned Byte - Register pre-indexed*)
    | word28 0 1 1 1 U_ B_ 1 L_ _ _ _ _ _ _ _ _ 0 0 0 0 0 0 0 0 _ _ _ _ ->
      decode_cond w (fun condition => M2_Register_pre_indexed U_ condition (regnum_from_bit n0 w) (regnum_from_bit n16 w))
    (*5.2.7 - Load and Store Word or Unsigned Byte - Scaled register pre-indexed*)
    | word28 0 1 1 1 U_ B_ 1 L_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 _ _ _ _ ->
      decode_cond w (fun condition => M2_Scaled_register_pre_indexed U_ condition (regnum_from_bit n0 w) (regnum_from_bit n16 w) (bits n6 n5 w) (bits n11 n7 w))
    (*5.2.8 - Load and Store Word or Unsigned Byte - Immediate post-indexed*)
    | word28 0 1 0 0 U_ B_ 0 L_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ->
      decode_cond w (fun condition => M2_Immediate_post_indexed U_ condition (regnum_from_bit n16 w) (bits n11 n0 w))
    (*5.2.9 - Load and Store Word or Unsigned Byte - Register post-indexed*)
    | word28 0 1 1 0 U_ B_ 0 L_ _ _ _ _ _ _ _ _ 0 0 0 0 0 0 0 0 _ _ _ _ ->
      decode_cond w (fun condition => M2_Register_post_indexed U_ condition (regnum_from_bit n0 w) (regnum_from_bit n16 w))
    (*5.2.10 - Load and Store Word or Unsigned Byte - Scaled register post-indexed*)
    | word28 0 1 1 0 U_ B_ 0 L_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 _ _ _ _ ->
      decode_cond w (fun condition => M2_Scaled_register_post_indexed U_ condition (regnum_from_bit n0 w) (regnum_from_bit n16 w) (bits n6 n5 w) (bits n11 n7 w))
    | _ -> DecError mode2 NotAnAddressingMode2
;;

let decode_addr_mode3 (w : word) =
 match w28_of_word w with
    (*5.3.2 - Miscellaneous Loads and Stores - Immediate offset*)
    | word28 0 0 0 1 U_ 1 0 L_ _ _ _ _ _ _ _ _ _ _ _ _ 1 S_ H_ 1 _ _ _ _ ->
      decode_cond w (fun condition => M3_Immediate_offset U_ (bits n11 n8 w) (bits n3 n0 w) (regnum_from_bit n16 w))
    (*5.3.3 - Miscellaneous Loads and Stores - Register offset*)
    | word28 0 0 0 1 U_ 0 0 L_ _ _ _ _ _ _ _ _ SBZ11 SBZ10 SBZ9 SBZ8 1 S_ H_ 1 _ _ _ _ ->
      decode_cond w (fun condition => M3_Register_offset U_ (regnum_from_bit n0 w) (regnum_from_bit n16 w))
    (*5.3.4 - Miscellaneous Loads and Stores - Immediate pre-indexed*)
    | word28 0 0 0 1 U_ 1 1 L_ _ _ _ _ _ _ _ _ _ _ _ _ 1 S_ H_ 1 _ _ _ _ ->
      decode_cond w (fun condition => M3_Immediate_pre_indexed U_ condition (bits n11 n8 w) (bits n3 n0 w) (regnum_from_bit n16 w))
    (*5.3.5 - Miscellaneous Loads and Stores - Register pre-indexed*)
    | word28 0 0 0 1 U_ 0 1 L_ _ _ _ _ _ _ _ _ SBZ11 SBZ10 SBZ9 SBZ8 1 S_ H_ 1 _ _ _ _ ->
      decode_cond w (fun condition => M3_Register_pre_indexed U_ condition (regnum_from_bit n0 w) (regnum_from_bit n16 w))
    (*5.3.6 - Miscellaneous Loads and Stores - Immediate post-indexed*)
    | word28 0 0 0 0 U_ 1 0 L_ _ _ _ _ _ _ _ _ _ _ _ _ 1 S_ H_ 1 _ _ _ _ ->
      decode_cond w (fun condition => M3_Immediate_post_indexed U_ condition (bits n11 n8 w) (bits n3 n0 w) (regnum_from_bit n16 w))
    (*5.3.7 - Miscellaneous Loads and Stores - Register post-indexed*)
    | word28 0 0 0 0 U_ 0 0 L_ _ _ _ _ _ _ _ _ SBZ11 SBZ10 SBZ9 SBZ8 1 S_ H_ 1 _ _ _ _ ->
      decode_cond w (fun condition => M3_Register_post_indexed U_ condition (regnum_from_bit n0 w) (regnum_from_bit n16 w))
    | _ -> DecError mode3 NotAnAddressingMode3
;;

let decode_addr_mode4 (w : word) =
 match w28_of_word w with
    (*5.4.2 - Load and Store Multiple - Increment after*)
    | word28 1 0 0 0 1 S_ W_ L_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ->
      decode_cond w (fun condition => M4_Increment_after W_ condition (regnum_from_bit n16 w) (bits n15 n0 w))
    (*5.4.3 - Load and Store Multiple - Increment before*)
    | word28 1 0 0 1 1 S_ W_ L_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ->
      decode_cond w (fun condition => M4_Increment_before W_ condition (regnum_from_bit n16 w) (bits n15 n0 w))
    (*5.4.4 - Load and Store Multiple - Decrement after*)
    | word28 1 0 0 0 0 S_ W_ L_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ->
      decode_cond w (fun condition => M4_Decrement_after W_ condition (regnum_from_bit n16 w) (bits n15 n0 w))
    (*5.4.5 - Load and Store Multiple - Decrement before*)
    | word28 1 0 0 1 0 S_ W_ L_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ->
      decode_cond w (fun condition => M4_Decrement_before W_ condition (regnum_from_bit n16 w) (bits n15 n0 w))
    | _ -> DecError mode4 NotAnAddressingMode4
;;

let decode_addr_mode5 (w : word) =
 match w28_of_word w with
    (*5.5.2 - Load and Store Coprocessor - Immediate offset*)
    | word28 1 1 0 1 U_ N_ 0 L_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ->
      decode_cond w (fun condition => M5_Immediate_offset U_ condition (bits n11 n8 w) (regnum_from_bit n16 w) (bits n7 n0 w))
    (*5.5.3 - Load and Store Coprocessor - Immediate pre-indexed*)
    | word28 1 1 0 1 U_ N_ 1 L_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ->
      decode_cond w (fun condition => M5_Immediate_pre_indexed U_ condition (bits n11 n8 w) (regnum_from_bit n16 w) (bits n7 n0 w))
    (*5.5.4 - Load and Store Coprocessor - Immediate post-indexed*)
    | word28 1 1 0 0 U_ N_ 1 L_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ->
      decode_cond w (fun condition => M5_Immediate_post_indexed U_ condition (bits n11 n8 w) (regnum_from_bit n16 w) (bits n7 n0 w))
    (*5.5.5 - Load and Store Coprocessor - Unindexed*)
    | word28 1 1 0 0 U_ N_ 0 L_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ->
      decode_cond w (fun condition => M5_Unindexed condition (bits n11 n8 w) (regnum_from_bit n16 w))
    | _ -> DecError mode5 NotAnAddressingMode5
;;

let decode_unconditional (w : word) =
  match w28_of_word w with
    (*4.1.8 - BLX (1)*)
    | word28 1 0 1 H_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ->
      decode_cond w (fun condition => BLX1 H_ (bits n23 n0 w))
    (*4.1.16 - CPS*)
    | word28 0 0 0 1 0 0 0 0 _ _ mmod 0 SBZ15 SBZ14 SBZ13 SBZ12 SBZ11 SBZ10 SBZ9 A_ I_ F_ 0 _ _ _ _ _ ->
      decode_cond w (fun condition => CPS A_ F_ I_ (bits n19 n18 w) mmod (bits n4 n0 w))
    (*4.1.45 - PLD*)
    | word28 0 1 I_ 1 U_ 1 0 1 _ _ _ _ 1 1 1 1 _ _ _ _ _ _ _ _ _ _ _ _ ->
      decode_cond_mode decode_addr_mode2 w (fun add_mode condition => PLD )
    (*4.1.59 - RFE*)
    | word28 1 0 0 P_ U_ 0 W_ 1 _ _ _ _ SBZ15 SBZ14 SBZ13 SBZ12 1 0 1 0 SBZ7 SBZ6 SBZ5 SBZ4 SBZ3 SBZ2 SBZ1 SBZ0 ->
      decode_cond_mode decode_addr_mode4 w (fun add_mode condition => RFE add_mode)
    (*4.1.67 - SETEND*)
    | word28 0 0 0 1 0 0 0 0 0 0 0 1 SBZ15 SBZ14 SBZ13 SBZ12 SBZ11 SBZ10 E_ SBZ8 0 0 0 0 SBZ3 SBZ2 SBZ1 SBZ0 ->
      decode_cond w (fun condition => SETEND E_)
    (*4.1.90 - SRS*)
    | word28 1 0 0 P_ U_ 1 W_ 0 1 1 0 1 SBZ15 SBZ14 SBZ13 SBZ12 0 1 0 1 SBZ7 SBZ6 SBZ5 _ _ _ _ _ ->
      decode_cond_mode decode_addr_mode4 w (fun add_mode condition => SRS add_mode)
    | _ => DecUndefined inst
;;

let decode_conditional (w : word) =
  match w28_of_word w with
    (*4.1.84 - SMMUL*)
    | word28 0 1 1 1 0 1 0 1 _ _ _ _ 1 1 1 1 _ _ _ _ 0 0 R_ 1 _ _ _ _ ->
      decode_cond w (fun condition => SMMUL R_ condition (regnum_from_bit n16 w) (regnum_from_bit n0 w) (regnum_from_bit n8 w))
    (*4.1.85 - SMUAD*)
    | word28 0 1 1 1 0 0 0 0 _ _ _ _ 1 1 1 1 _ _ _ _ 0 0 X_ 1 _ _ _ _ ->
      decode_cond w (fun condition => SMUAD X_ condition (regnum_from_bit n16 w) (regnum_from_bit n0 w) (regnum_from_bit n8 w))
    (*4.1.86 - SMUL<x><y>*)
    | word28 0 0 0 1 0 1 1 0 _ _ _ _ SBZ15 SBZ14 SBZ13 SBZ12 _ _ _ _ 1 y_ x_ 0 _ _ _ _ ->
      decode_cond w (fun condition => SMULxy condition (regnum_from_bit n16 w) (regnum_from_bit n0 w) (regnum_from_bit n8 w) x_ y_)
    (*4.1.87 - SMULL*)
    | word28 0 0 0 0 1 1 0 S_ _ _ _ _ _ _ _ _ _ _ _ _ 1 0 0 1 _ _ _ _ ->
      decode_cond w (fun condition => SMULL S_ condition (regnum_from_bit n16 w) (regnum_from_bit n12 w) (regnum_from_bit n0 w) (regnum_from_bit n8 w))
    (*4.1.88 - SMULW<y>*)
    | word28 0 0 0 1 0 0 1 0 _ _ _ _ SBZ15 SBZ14 SBZ13 SBZ12 _ _ _ _ 1 y_ 1 0 _ _ _ _ ->
      decode_cond w (fun condition => SMULWy condition (regnum_from_bit n16 w) (regnum_from_bit n0 w) (regnum_from_bit n8 w) y_)
    (*4.1.89 - SMUSD*)
    | word28 0 1 1 1 0 0 0 0 _ _ _ _ 1 1 1 1 _ _ _ _ 0 1 X_ 1 _ _ _ _ ->
      decode_cond w (fun condition => SMUSD X_ condition (regnum_from_bit n16 w) (regnum_from_bit n0 w) (regnum_from_bit n8 w))
    (*4.1.113 - SXTB*)
    | word28 0 1 1 0 1 0 1 0 1 1 1 1 _ _ _ _ _ _ SBZ9 SBZ8 0 1 1 1 _ _ _ _ ->
      decode_cond w (fun condition => SXTB condition (regnum_from_bit n12 w) (regnum_from_bit n0 w) (bits n11 n10 w))
    (*4.1.114 - SXTB16*)
    | word28 0 1 1 0 1 0 0 0 1 1 1 1 _ _ _ _ _ _ SBZ9 SBZ8 0 1 1 1 _ _ _ _ ->
      decode_cond w (fun condition => SXTB16 condition (regnum_from_bit n12 w) (regnum_from_bit n0 w) (bits n11 n10 w))
    (*4.1.115 - SXTH*)
    | word28 0 1 1 0 1 0 1 1 1 1 1 1 _ _ _ _ _ _ SBZ9 SBZ8 0 1 1 1 _ _ _ _ ->
      decode_cond w (fun condition => SXTH condition (regnum_from_bit n12 w) (regnum_from_bit n0 w) (bits n11 n10 w))
    (*4.1.129 - UMULL*)
    | word28 0 0 0 0 1 0 0 S_ _ _ _ _ _ _ _ _ _ _ _ _ 1 0 0 1 _ _ _ _ ->
      decode_cond w (fun condition => UMULL S_ condition (regnum_from_bit n16 w) (regnum_from_bit n12 w) (regnum_from_bit n0 w) (regnum_from_bit n8 w))
    (*4.1.146 - UXTB*)
    | word28 0 1 1 0 1 1 1 0 1 1 1 1 _ _ _ _ _ _ SBZ9 SBZ8 0 1 1 1 _ _ _ _ ->
      decode_cond w (fun condition => UXTB condition (regnum_from_bit n12 w) (regnum_from_bit n0 w) (bits n11 n10 w))
    (*4.1.147 - UXTB16*)
    | word28 0 1 1 0 1 1 0 0 1 1 1 1 _ _ _ _ _ _ SBZ9 SBZ8 0 1 1 1 _ _ _ _ ->
      decode_cond w (fun condition => UXTB16 condition (regnum_from_bit n12 w) (regnum_from_bit n0 w) (bits n11 n10 w))
    (*4.1.148 - UXTH*)
    | word28 0 1 1 0 1 1 1 1 1 1 1 1 _ _ _ _ _ _ SBZ9 SBZ8 0 1 1 1 _ _ _ _ ->
      decode_cond w (fun condition => UXTH condition (regnum_from_bit n12 w) (regnum_from_bit n0 w) (bits n11 n10 w))
    (*4.1.5 - B, BL*)
    | word28 1 0 1 L_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ->
      decode_cond w (fun condition => B L_ condition (bits n23 n0 w))
    (*4.1.7 - BKPT*)
    | word28 0 0 0 1 0 0 1 0 _ _ _ _ _ _ _ _ _ _ _ _ 0 1 1 1 _ _ _ _ ->
      decode_cond w (fun condition => BKPT )
    (*4.1.12 - CDP*)
    | word28 1 1 1 0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 _ _ _ _ ->
      decode_cond w (fun condition => CDP condition (bits n11 n8 w))
    (*4.1.17 - CPY*)
    | word28 0 0 0 1 1 0 1 0 SBZ19 SBZ18 SBZ17 SBZ16 _ _ _ _ 0 0 0 0 0 0 0 0 _ _ _ _ ->
      decode_cond w (fun condition => CPY condition (regnum_from_bit n12 w) (regnum_from_bit n0 w))
    (*4.1.27 - LDREX*)
    | word28 0 0 0 1 1 0 0 1 _ _ _ _ _ _ _ _ SBO11 SBO10 SBO9 SBO8 1 0 0 1 SBO3 SBO2 SBO1 SBO0 ->
      decode_cond w (fun condition => LDREX condition (regnum_from_bit n12 w) (regnum_from_bit n16 w))
    (*4.1.32 - MCR*)
    | word28 1 1 1 0 _ _ _ 0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 1 _ _ _ _ ->
      decode_cond w (fun condition => MCR condition (bits n11 n8 w) (regnum_from_bit n12 w))
    (*4.1.33 - MCRR*)
    | word28 1 1 0 0 0 1 0 0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ->
      decode_cond w (fun condition => MCRR condition (bits n11 n8 w) (regnum_from_bit n12 w) (regnum_from_bit n16 w))
    (*4.1.34 - MLA*)
    | word28 0 0 0 0 0 0 1 S_ _ _ _ _ _ _ _ _ _ _ _ _ 1 0 0 1 _ _ _ _ ->
      decode_cond w (fun condition => MLA S_ condition (regnum_from_bit n16 w) (regnum_from_bit n0 w) (regnum_from_bit n12 w) (regnum_from_bit n8 w))
    (*4.1.36 - MRC*)
    | word28 1 1 1 0 _ _ _ 1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 1 _ _ _ _ ->
      decode_cond w (fun condition => MRC condition (bits n11 n8 w) (regnum_from_bit n12 w))
    (*4.1.37 - MRRC*)
    | word28 1 1 0 0 0 1 0 1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ->
      decode_cond w (fun condition => MRRC condition (bits n11 n8 w) (regnum_from_bit n12 w) (regnum_from_bit n16 w))
    (*4.1.43 - PKHBT*)
    | word28 0 1 1 0 1 0 0 0 _ _ _ _ _ _ _ _ _ _ _ _ _ 0 0 1 _ _ _ _ ->
      decode_cond w (fun condition => PKHBT condition (regnum_from_bit n12 w) (regnum_from_bit n0 w) (regnum_from_bit n16 w) (bits n11 n7 w))
    (*4.1.44 - PKHTB*)
    | word28 0 1 1 0 1 0 0 0 _ _ _ _ _ _ _ _ _ _ _ _ _ 1 0 1 _ _ _ _ ->
      decode_cond w (fun condition => PKHTB condition (regnum_from_bit n12 w) (regnum_from_bit n0 w) (regnum_from_bit n16 w) (bits n11 n7 w))
    (*4.1.46 - QADD*)
    | word28 0 0 0 1 0 0 0 0 _ _ _ _ _ _ _ _ SBZ11 SBZ10 SBZ9 SBZ8 0 1 0 1 _ _ _ _ ->
      decode_cond w (fun condition => QADD condition (regnum_from_bit n12 w) (regnum_from_bit n0 w) (regnum_from_bit n16 w))
    (*4.1.47 - QADD16*)
    | word28 0 1 1 0 0 0 1 0 _ _ _ _ _ _ _ _ SBO11 SBO10 SBO9 SBO8 0 0 0 1 _ _ _ _ ->
      decode_cond w (fun condition => QADD16 condition (regnum_from_bit n12 w) (regnum_from_bit n0 w) (regnum_from_bit n16 w))
    (*4.1.48 - QADD8*)
    | word28 0 1 1 0 0 0 1 0 _ _ _ _ _ _ _ _ SBO11 SBO10 SBO9 SBO8 1 0 0 1 _ _ _ _ ->
      decode_cond w (fun condition => QADD8 condition (regnum_from_bit n12 w) (regnum_from_bit n0 w) (regnum_from_bit n16 w))
    (*4.1.49 - QADDSUBX*)
    | word28 0 1 1 0 0 0 1 0 _ _ _ _ _ _ _ _ SBO11 SBO10 SBO9 SBO8 0 0 1 1 _ _ _ _ ->
      decode_cond w (fun condition => QADDSUBX condition (regnum_from_bit n12 w) (regnum_from_bit n0 w) (regnum_from_bit n16 w))
    (*4.1.50 - QDADD*)
    | word28 0 0 0 1 0 1 0 0 _ _ _ _ _ _ _ _ SBZ11 SBZ10 SBZ9 SBZ8 0 1 0 1 _ _ _ _ ->
      decode_cond w (fun condition => QDADD condition (regnum_from_bit n12 w) (regnum_from_bit n0 w) (regnum_from_bit n16 w))
    (*4.1.51 - QDSUB*)
    | word28 0 0 0 1 0 1 1 0 _ _ _ _ _ _ _ _ SBZ11 SBZ10 SBZ9 SBZ8 0 1 0 1 _ _ _ _ ->
      decode_cond w (fun condition => QDSUB condition (regnum_from_bit n12 w) (regnum_from_bit n0 w) (regnum_from_bit n16 w))
    (*4.1.52 - QSUB*)
    | word28 0 0 0 1 0 0 1 0 _ _ _ _ _ _ _ _ SBZ11 SBZ10 SBZ9 SBZ8 0 1 0 1 _ _ _ _ ->
      decode_cond w (fun condition => QSUB condition (regnum_from_bit n12 w) (regnum_from_bit n0 w) (regnum_from_bit n16 w))
    (*4.1.53 - QSUB16*)
    | word28 0 1 1 0 0 0 1 0 _ _ _ _ _ _ _ _ SBO11 SBO10 SBO9 SBO8 0 1 1 1 _ _ _ _ ->
      decode_cond w (fun condition => QSUB16 condition (regnum_from_bit n12 w) (regnum_from_bit n0 w) (regnum_from_bit n16 w))
    (*4.1.54 - QSUB8*)
    | word28 0 1 1 0 0 0 1 0 _ _ _ _ _ _ _ _ SBO11 SBO10 SBO9 SBO8 1 1 1 1 _ _ _ _ ->
      decode_cond w (fun condition => QSUB8 condition (regnum_from_bit n12 w) (regnum_from_bit n0 w) (regnum_from_bit n16 w))
    (*4.1.55 - QSUBADDX*)
    | word28 0 1 1 0 0 0 1 0 _ _ _ _ _ _ _ _ SBO11 SBO10 SBO9 SBO8 0 1 0 1 _ _ _ _ ->
      decode_cond w (fun condition => QSUBADDX condition (regnum_from_bit n12 w) (regnum_from_bit n0 w) (regnum_from_bit n16 w))
    (*4.1.56 - REV*)
    | word28 0 1 1 0 1 0 1 1 SBO19 SBO18 SBO17 SBO16 _ _ _ _ SBO11 SBO10 SBO9 SBO8 0 0 1 1 _ _ _ _ ->
      decode_cond w (fun condition => REV condition (regnum_from_bit n12 w) (regnum_from_bit n0 w))
    (*4.1.57 - REV16*)
    | word28 0 1 1 0 1 0 1 1 SBO19 SBO18 SBO17 SBO16 _ _ _ _ SBO11 SBO10 SBO9 SBO8 1 0 1 1 _ _ _ _ ->
      decode_cond w (fun condition => REV16 condition (regnum_from_bit n12 w) (regnum_from_bit n0 w))
    (*4.1.58 - REVSH*)
    | word28 0 1 1 0 1 1 1 1 SBO19 SBO18 SBO17 SBO16 _ _ _ _ SBO11 SBO10 SBO9 SBO8 1 0 1 1 _ _ _ _ ->
      decode_cond w (fun condition => REVSH condition (regnum_from_bit n12 w) (regnum_from_bit n0 w))
    (*4.1.62 - SADD16*)
    | word28 0 1 1 0 0 0 0 1 _ _ _ _ _ _ _ _ SBO11 SBO10 SBO9 SBO8 0 0 0 1 _ _ _ _ ->
      decode_cond w (fun condition => SADD16 condition (regnum_from_bit n12 w) (regnum_from_bit n0 w) (regnum_from_bit n16 w))
    (*4.1.63 - SADD8*)
    | word28 0 1 1 0 0 0 0 1 _ _ _ _ _ _ _ _ SBO11 SBO10 SBO9 SBO8 1 0 0 1 _ _ _ _ ->
      decode_cond w (fun condition => SADD8 condition (regnum_from_bit n12 w) (regnum_from_bit n0 w) (regnum_from_bit n16 w))
    (*4.1.64 - SADDSUBX*)
    | word28 0 1 1 0 0 0 0 1 _ _ _ _ _ _ _ _ SBO11 SBO10 SBO9 SBO8 0 0 1 1 _ _ _ _ ->
      decode_cond w (fun condition => SADDSUBX condition (regnum_from_bit n12 w) (regnum_from_bit n0 w) (regnum_from_bit n16 w))
    (*4.1.66 - SEL*)
    | word28 0 1 1 0 1 0 0 0 _ _ _ _ _ _ _ _ SBO11 SBO10 SBO9 SBO8 1 0 1 1 _ _ _ _ ->
      decode_cond w (fun condition => SEL condition (regnum_from_bit n12 w) (regnum_from_bit n0 w) (regnum_from_bit n16 w))
    (*4.1.68 - SHADD16*)
    | word28 0 1 1 0 0 0 1 1 _ _ _ _ _ _ _ _ SBO11 SBO10 SBO9 SBO8 0 0 0 1 _ _ _ _ ->
      decode_cond w (fun condition => SHADD16 condition (regnum_from_bit n12 w) (regnum_from_bit n0 w) (regnum_from_bit n16 w))
    (*4.1.69 - SHADD8*)
    | word28 0 1 1 0 0 0 1 1 _ _ _ _ _ _ _ _ SBO11 SBO10 SBO9 SBO8 1 0 0 1 _ _ _ _ ->
      decode_cond w (fun condition => SHADD8 condition (regnum_from_bit n12 w) (regnum_from_bit n0 w) (regnum_from_bit n16 w))
    (*4.1.70 - SHADDSUBX*)
    | word28 0 1 1 0 0 0 1 1 _ _ _ _ _ _ _ _ SBO11 SBO10 SBO9 SBO8 0 0 1 1 _ _ _ _ ->
      decode_cond w (fun condition => SHADDSUBX condition (regnum_from_bit n12 w) (regnum_from_bit n0 w) (regnum_from_bit n16 w))
    (*4.1.71 - SHSUB16*)
    | word28 0 1 1 0 0 0 1 1 _ _ _ _ _ _ _ _ SBO11 SBO10 SBO9 SBO8 0 1 1 1 _ _ _ _ ->
      decode_cond w (fun condition => SHSUB16 condition (regnum_from_bit n12 w) (regnum_from_bit n0 w) (regnum_from_bit n16 w))
    (*4.1.72 - SHSUB8*)
    | word28 0 1 1 0 0 0 1 1 _ _ _ _ _ _ _ _ SBO11 SBO10 SBO9 SBO8 1 1 1 1 _ _ _ _ ->
      decode_cond w (fun condition => SHSUB8 condition (regnum_from_bit n12 w) (regnum_from_bit n0 w) (regnum_from_bit n16 w))
    (*4.1.73 - SHSUBADDX*)
    | word28 0 1 1 0 0 0 1 1 _ _ _ _ _ _ _ _ SBO11 SBO10 SBO9 SBO8 0 1 0 1 _ _ _ _ ->
      decode_cond w (fun condition => SHSUBADDX condition (regnum_from_bit n12 w) (regnum_from_bit n0 w) (regnum_from_bit n16 w))
    (*4.1.74 - SMLA<x><y>*)
    | word28 0 0 0 1 0 0 0 0 _ _ _ _ _ _ _ _ _ _ _ _ 1 y_ x_ 0 _ _ _ _ ->
      decode_cond w (fun condition => SMLAxy condition (regnum_from_bit n16 w) (regnum_from_bit n0 w) (regnum_from_bit n12 w) (regnum_from_bit n8 w) x_ y_)
    (*4.1.75 - SMLAD*)
    | word28 0 1 1 1 0 0 0 0 _ _ _ _ _ _ _ _ _ _ _ _ 0 0 X_ 1 _ _ _ _ ->
      decode_cond w (fun condition => SMLAD X_ condition (regnum_from_bit n16 w) (regnum_from_bit n0 w) (regnum_from_bit n12 w) (regnum_from_bit n8 w))
    (*4.1.76 - SMLAL*)
    | word28 0 0 0 0 1 1 1 S_ _ _ _ _ _ _ _ _ _ _ _ _ 1 0 0 1 _ _ _ _ ->
      decode_cond w (fun condition => SMLAL S_ condition (regnum_from_bit n16 w) (regnum_from_bit n12 w) (regnum_from_bit n0 w) (regnum_from_bit n8 w))
    (*4.1.77 - SMLAL<x><y>*)
    | word28 0 0 0 1 0 1 0 0 _ _ _ _ _ _ _ _ _ _ _ _ 1 y_ x_ 0 _ _ _ _ ->
      decode_cond w (fun condition => SMLALxy condition (regnum_from_bit n16 w) (regnum_from_bit n12 w) (regnum_from_bit n0 w) (regnum_from_bit n8 w) x_ y_)
    (*4.1.78 - SMLALD*)
    | word28 0 1 1 1 0 1 0 0 _ _ _ _ _ _ _ _ _ _ _ _ 0 0 X_ 1 _ _ _ _ ->
      decode_cond w (fun condition => SMLALD X_ condition (regnum_from_bit n16 w) (regnum_from_bit n12 w) (regnum_from_bit n0 w) (regnum_from_bit n8 w))
    (*4.1.79 - SMLAW<y>*)
    | word28 0 0 0 1 0 0 1 0 _ _ _ _ _ _ _ _ _ _ _ _ 1 y_ 0 0 _ _ _ _ ->
      decode_cond w (fun condition => SMLAWy condition (regnum_from_bit n16 w) (regnum_from_bit n0 w) (regnum_from_bit n12 w) (regnum_from_bit n8 w) y_)
    (*4.1.80 - SMLSD*)
    | word28 0 1 1 1 0 0 0 0 _ _ _ _ _ _ _ _ _ _ _ _ 0 1 X_ 1 _ _ _ _ ->
      decode_cond w (fun condition => SMLSD X_ condition (regnum_from_bit n16 w) (regnum_from_bit n0 w) (regnum_from_bit n12 w) (regnum_from_bit n8 w))
    (*4.1.81 - SMLSLD*)
    | word28 0 1 1 1 0 1 0 0 _ _ _ _ _ _ _ _ _ _ _ _ 0 1 X_ 1 _ _ _ _ ->
      decode_cond w (fun condition => SMLSLD X_ condition (regnum_from_bit n16 w) (regnum_from_bit n12 w) (regnum_from_bit n0 w) (regnum_from_bit n8 w))
    (*4.1.82 - SMMLA*)
    | word28 0 1 1 1 0 1 0 1 _ _ _ _ _ _ _ _ _ _ _ _ 0 0 R_ 1 _ _ _ _ ->
      decode_cond w (fun condition => SMMLA R_ condition (regnum_from_bit n16 w) (regnum_from_bit n0 w) (regnum_from_bit n12 w) (regnum_from_bit n8 w))
    (*4.1.83 - SMMLS*)
    | word28 0 1 1 1 0 1 0 1 _ _ _ _ _ _ _ _ _ _ _ _ 1 1 R_ 1 _ _ _ _ ->
      decode_cond w (fun condition => SMMLS R_ condition (regnum_from_bit n16 w) (regnum_from_bit n0 w) (regnum_from_bit n12 w) (regnum_from_bit n8 w))
    (*4.1.91 - SSAT*)
    | word28 0 1 1 0 1 0 1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ sh 0 1 _ _ _ _ ->
      decode_cond w (fun condition => SSAT condition (regnum_from_bit n12 w) (regnum_from_bit n0 w) (bits n20 n16 w) sh (bits n11 n7 w))
    (*4.1.92 - SSAT16*)
    | word28 0 1 1 0 1 0 1 0 _ _ _ _ _ _ _ _ SBO11 SBO10 SBO9 SBO8 0 0 1 1 _ _ _ _ ->
      decode_cond w (fun condition => SSAT16 condition (regnum_from_bit n12 w) (regnum_from_bit n0 w) (bits n19 n16 w))
    (*4.1.93 - SSUB16*)
    | word28 0 1 1 0 0 0 0 1 _ _ _ _ _ _ _ _ SBO11 SBO10 SBO9 SBO8 0 1 1 1 _ _ _ _ ->
      decode_cond w (fun condition => SSUB16 condition (regnum_from_bit n12 w) (regnum_from_bit n0 w) (regnum_from_bit n16 w))
    (*4.1.94 - SSUB8*)
    | word28 0 1 1 0 0 0 0 1 _ _ _ _ _ _ _ _ SBO11 SBO10 SBO9 SBO8 1 1 1 1 _ _ _ _ ->
      decode_cond w (fun condition => SSUB8 condition (regnum_from_bit n12 w) (regnum_from_bit n0 w) (regnum_from_bit n16 w))
    (*4.1.95 - SSUBADDX*)
    | word28 0 1 1 0 0 0 0 1 _ _ _ _ _ _ _ _ SBO11 SBO10 SBO9 SBO8 0 1 0 1 _ _ _ _ ->
      decode_cond w (fun condition => SSUBADDX condition (regnum_from_bit n12 w) (regnum_from_bit n0 w) (regnum_from_bit n16 w))
    (*4.1.103 - STREX*)
    | word28 0 0 0 1 1 0 0 0 _ _ _ _ _ _ _ _ SBO11 SBO10 SBO9 SBO8 1 0 0 1 _ _ _ _ ->
      decode_cond w (fun condition => STREX condition (regnum_from_bit n12 w) (regnum_from_bit n0 w) (regnum_from_bit n16 w))
    (*4.1.107 - SWI*)
    | word28 1 1 1 1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ->
      decode_cond w (fun condition => SWI condition)
    (*4.1.108 - SWP*)
    | word28 0 0 0 1 0 0 0 0 _ _ _ _ _ _ _ _ SBZ11 SBZ10 SBZ9 SBZ8 1 0 0 1 _ _ _ _ ->
      decode_cond w (fun condition => SWP condition (regnum_from_bit n12 w) (regnum_from_bit n0 w) (regnum_from_bit n16 w))
    (*4.1.109 - SWPB*)
    | word28 0 0 0 1 0 1 0 0 _ _ _ _ _ _ _ _ SBZ11 SBZ10 SBZ9 SBZ8 1 0 0 1 _ _ _ _ ->
      decode_cond w (fun condition => SWPB condition (regnum_from_bit n12 w) (regnum_from_bit n0 w) (regnum_from_bit n16 w))
    (*4.1.110 - SXTAB*)
    | word28 0 1 1 0 1 0 1 0 _ _ _ _ _ _ _ _ _ _ SBZ9 SBZ8 0 1 1 1 _ _ _ _ ->
      decode_cond w (fun condition => SXTAB condition (regnum_from_bit n12 w) (regnum_from_bit n0 w) (regnum_from_bit n16 w) (bits n11 n10 w))
    (*4.1.111 - SXTAB16*)
    | word28 0 1 1 0 1 0 0 0 _ _ _ _ _ _ _ _ _ _ SBZ9 SBZ8 0 1 1 1 _ _ _ _ ->
      decode_cond w (fun condition => SXTAB16 condition (regnum_from_bit n12 w) (regnum_from_bit n0 w) (regnum_from_bit n16 w) (bits n11 n10 w))
    (*4.1.112 - SXTAH*)
    | word28 0 1 1 0 1 0 1 1 _ _ _ _ _ _ _ _ _ _ SBZ9 SBZ8 0 1 1 1 _ _ _ _ ->
      decode_cond w (fun condition => SXTAH condition (regnum_from_bit n12 w) (regnum_from_bit n0 w) (regnum_from_bit n16 w) (bits n11 n10 w))
    (*4.1.118 - UADD16*)
    | word28 0 1 1 0 0 1 0 1 _ _ _ _ _ _ _ _ SBO11 SBO10 SBO9 SBO8 0 0 0 1 _ _ _ _ ->
      decode_cond w (fun condition => UADD16 condition (regnum_from_bit n12 w) (regnum_from_bit n0 w) (regnum_from_bit n16 w))
    (*4.1.119 - UADD8*)
    | word28 0 1 1 0 0 1 0 1 _ _ _ _ _ _ _ _ SBO11 SBO10 SBO9 SBO8 1 0 0 1 _ _ _ _ ->
      decode_cond w (fun condition => UADD8 condition (regnum_from_bit n12 w) (regnum_from_bit n0 w) (regnum_from_bit n16 w))
    (*4.1.120 - UADDSUBX*)
    | word28 0 1 1 0 0 1 0 1 _ _ _ _ _ _ _ _ SBO11 SBO10 SBO9 SBO8 0 0 1 1 _ _ _ _ ->
      decode_cond w (fun condition => UADDSUBX condition (regnum_from_bit n12 w) (regnum_from_bit n0 w) (regnum_from_bit n16 w))
    (*4.1.121 - UHADD16*)
    | word28 0 1 1 0 0 1 1 1 _ _ _ _ _ _ _ _ SBO11 SBO10 SBO9 SBO8 0 0 0 1 _ _ _ _ ->
      decode_cond w (fun condition => UHADD16 condition (regnum_from_bit n12 w) (regnum_from_bit n0 w) (regnum_from_bit n16 w))
    (*4.1.122 - UHADD8*)
    | word28 0 1 1 0 0 1 1 1 _ _ _ _ _ _ _ _ SBO11 SBO10 SBO9 SBO8 1 0 0 1 _ _ _ _ ->
      decode_cond w (fun condition => UHADD8 condition (regnum_from_bit n12 w) (regnum_from_bit n0 w) (regnum_from_bit n16 w))
    (*4.1.123 - UHADDSUBX*)
    | word28 0 1 1 0 0 1 1 1 _ _ _ _ _ _ _ _ SBO11 SBO10 SBO9 SBO8 0 0 1 1 _ _ _ _ ->
      decode_cond w (fun condition => UHADDSUBX condition (regnum_from_bit n12 w) (regnum_from_bit n0 w) (regnum_from_bit n16 w))
    (*4.1.124 - UHSUB16*)
    | word28 0 1 1 0 0 1 1 1 _ _ _ _ _ _ _ _ SBO11 SBO10 SBO9 SBO8 0 1 1 1 _ _ _ _ ->
      decode_cond w (fun condition => UHSUB16 condition (regnum_from_bit n12 w) (regnum_from_bit n0 w) (regnum_from_bit n16 w))
    (*4.1.125 - UHSUB8*)
    | word28 0 1 1 0 0 1 1 1 _ _ _ _ _ _ _ _ SBO11 SBO10 SBO9 SBO8 1 1 1 1 _ _ _ _ ->
      decode_cond w (fun condition => UHSUB8 condition (regnum_from_bit n12 w) (regnum_from_bit n0 w) (regnum_from_bit n16 w))
    (*4.1.126 - UHSUBADDX*)
    | word28 0 1 1 0 0 1 1 1 _ _ _ _ _ _ _ _ SBO11 SBO10 SBO9 SBO8 0 1 0 1 _ _ _ _ ->
      decode_cond w (fun condition => UHSUBADDX condition (regnum_from_bit n12 w) (regnum_from_bit n0 w) (regnum_from_bit n16 w))
    (*4.1.127 - UMAAL*)
    | word28 0 0 0 0 0 1 0 0 _ _ _ _ _ _ _ _ _ _ _ _ 1 0 0 1 _ _ _ _ ->
      decode_cond w (fun condition => UMAAL condition (regnum_from_bit n16 w) (regnum_from_bit n12 w) (regnum_from_bit n0 w) (regnum_from_bit n8 w))
    (*4.1.128 - UMLAL*)
    | word28 0 0 0 0 1 0 1 S_ _ _ _ _ _ _ _ _ _ _ _ _ 1 0 0 1 _ _ _ _ ->
      decode_cond w (fun condition => UMLAL S_ condition (regnum_from_bit n16 w) (regnum_from_bit n12 w) (regnum_from_bit n0 w) (regnum_from_bit n8 w))
    (*4.1.130 - UQADD16*)
    | word28 0 1 1 0 0 1 1 0 _ _ _ _ _ _ _ _ SBO11 SBO10 SBO9 SBO8 0 0 0 1 _ _ _ _ ->
      decode_cond w (fun condition => UQADD16 condition (regnum_from_bit n12 w) (regnum_from_bit n0 w) (regnum_from_bit n16 w))
    (*4.1.131 - UQADD8*)
    | word28 0 1 1 0 0 1 1 0 _ _ _ _ _ _ _ _ SBO11 SBO10 SBO9 SBO8 1 0 0 1 _ _ _ _ ->
      decode_cond w (fun condition => UQADD8 condition (regnum_from_bit n12 w) (regnum_from_bit n0 w) (regnum_from_bit n16 w))
    (*4.1.132 - UQADDSUBX*)
    | word28 0 1 1 0 0 1 1 0 _ _ _ _ _ _ _ _ SBO11 SBO10 SBO9 SBO8 0 0 1 1 _ _ _ _ ->
      decode_cond w (fun condition => UQADDSUBX condition (regnum_from_bit n12 w) (regnum_from_bit n0 w) (regnum_from_bit n16 w))
    (*4.1.133 - UQSUB16*)
    | word28 0 1 1 0 0 1 1 0 _ _ _ _ _ _ _ _ SBO11 SBO10 SBO9 SBO8 0 1 1 1 _ _ _ _ ->
      decode_cond w (fun condition => UQSUB16 condition (regnum_from_bit n12 w) (regnum_from_bit n0 w) (regnum_from_bit n16 w))
    (*4.1.134 - UQSUB8*)
    | word28 0 1 1 0 0 1 1 0 _ _ _ _ _ _ _ _ SBO11 SBO10 SBO9 SBO8 1 1 1 1 _ _ _ _ ->
      decode_cond w (fun condition => UQSUB8 condition (regnum_from_bit n12 w) (regnum_from_bit n0 w) (regnum_from_bit n16 w))
    (*4.1.135 - UQSUBADDX*)
    | word28 0 1 1 0 0 1 1 0 _ _ _ _ _ _ _ _ SBO11 SBO10 SBO9 SBO8 0 1 0 1 _ _ _ _ ->
      decode_cond w (fun condition => UQSUBADDX condition (regnum_from_bit n12 w) (regnum_from_bit n0 w) (regnum_from_bit n16 w))
    (*4.1.136 - USAD8*)
    | word28 0 1 1 1 1 0 0 0 _ _ _ _ 1 1 1 1 _ _ _ _ 0 0 0 1 _ _ _ _ ->
      decode_cond w (fun condition => USAD8 condition (regnum_from_bit n16 w) (regnum_from_bit n0 w) (regnum_from_bit n8 w))
    (*4.1.137 - USADA8*)
    | word28 0 1 1 1 1 0 0 0 _ _ _ _ _ _ _ _ _ _ _ _ 0 0 0 1 _ _ _ _ ->
      decode_cond w (fun condition => USADA8 condition (regnum_from_bit n16 w) (regnum_from_bit n0 w) (regnum_from_bit n12 w) (regnum_from_bit n8 w))
    (*4.1.138 - USAT*)
    | word28 0 1 1 0 1 1 1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ sh 0 1 _ _ _ _ ->
      decode_cond w (fun condition => USAT condition (regnum_from_bit n12 w) (regnum_from_bit n0 w) (bits n20 n16 w) sh (bits n11 n7 w))
    (*4.1.139 - USAT16*)
    | word28 0 1 1 0 1 1 1 0 _ _ _ _ _ _ _ _ SBO11 SBO10 SBO9 SBO8 0 0 1 1 _ _ _ _ ->
      decode_cond w (fun condition => USAT16 condition (regnum_from_bit n12 w) (regnum_from_bit n0 w) (bits n19 n16 w))
    (*4.1.140 - USUB16*)
    | word28 0 1 1 0 0 1 0 1 _ _ _ _ _ _ _ _ SBO11 SBO10 SBO9 SBO8 0 1 1 1 _ _ _ _ ->
      decode_cond w (fun condition => USUB16 condition (regnum_from_bit n12 w) (regnum_from_bit n0 w) (regnum_from_bit n16 w))
    (*4.1.141 - USUB8*)
    | word28 0 1 1 0 0 1 0 1 _ _ _ _ _ _ _ _ SBO11 SBO10 SBO9 SBO8 1 1 1 1 _ _ _ _ ->
      decode_cond w (fun condition => USUB8 condition (regnum_from_bit n12 w) (regnum_from_bit n0 w) (regnum_from_bit n16 w))
    (*4.1.142 - USUBADDX*)
    | word28 0 1 1 0 0 1 0 1 _ _ _ _ _ _ _ _ SBO11 SBO10 SBO9 SBO8 0 1 0 1 _ _ _ _ ->
      decode_cond w (fun condition => USUBADDX condition (regnum_from_bit n12 w) (regnum_from_bit n0 w) (regnum_from_bit n16 w))
    (*4.1.143 - UXTAB*)
    | word28 0 1 1 0 1 1 1 0 _ _ _ _ _ _ _ _ _ _ SBZ9 SBZ8 0 1 1 1 _ _ _ _ ->
      decode_cond w (fun condition => UXTAB condition (regnum_from_bit n12 w) (regnum_from_bit n0 w) (regnum_from_bit n16 w) (bits n11 n10 w))
    (*4.1.144 - UXTAB16*)
    | word28 0 1 1 0 1 1 0 0 _ _ _ _ _ _ _ _ _ _ SBZ9 SBZ8 0 1 1 1 _ _ _ _ ->
      decode_cond w (fun condition => UXTAB16 condition (regnum_from_bit n12 w) (regnum_from_bit n0 w) (regnum_from_bit n16 w) (bits n11 n10 w))
    (*4.1.145 - UXTAH*)
    | word28 0 1 1 0 1 1 1 1 _ _ _ _ _ _ _ _ _ _ SBZ9 SBZ8 0 1 1 1 _ _ _ _ ->
      decode_cond w (fun condition => UXTAH condition (regnum_from_bit n12 w) (regnum_from_bit n0 w) (regnum_from_bit n16 w) (bits n11 n10 w))
    (*4.1.9 - BLX (2)*)
    | word28 0 0 0 1 0 0 1 0 SBO19 SBO18 SBO17 SBO16 SBO15 SBO14 SBO13 SBO12 SBO11 SBO10 SBO9 SBO8 0 0 1 1 _ _ _ _ ->
      decode_cond w (fun condition => BLX2 condition (regnum_from_bit n0 w))
    (*4.1.10 - BX*)
    | word28 0 0 0 1 0 0 1 0 SBO19 SBO18 SBO17 SBO16 SBO15 SBO14 SBO13 SBO12 SBO11 SBO10 SBO9 SBO8 0 0 0 1 _ _ _ _ ->
      decode_cond w (fun condition => BX condition (regnum_from_bit n0 w))
    (*4.1.11 - BXJ*)
    | word28 0 0 0 1 0 0 1 0 SBO19 SBO18 SBO17 SBO16 SBO15 SBO14 SBO13 SBO12 SBO11 SBO10 SBO9 SBO8 0 0 1 0 _ _ _ _ ->
      decode_cond w (fun condition => BXJ condition (regnum_from_bit n0 w))
    (*4.1.13 - CLZ*)
    | word28 0 0 0 1 0 1 1 0 SBO19 SBO18 SBO17 SBO16 _ _ _ _ SBO11 SBO10 SBO9 SBO8 0 0 0 1 _ _ _ _ ->
      decode_cond w (fun condition => CLZ condition (regnum_from_bit n12 w) (regnum_from_bit n0 w))
    (*4.1.39.1 - MSR  Immediate operand:*)
    | word28 0 0 1 1 0 R_ 1 0 _ _ _ _ SBO15 SBO14 SBO13 SBO12 _ _ _ _ _ _ _ _ _ _ _ _ ->
      decode_cond w (fun condition => MSRimm R_ condition (bits n19 n16 w) (bits n7 n0 w) (bits n11 n8 w))
    (*4.1.39.2 - MSR  Register operand:*)
    | word28 0 0 0 1 0 R_ 1 0 _ _ _ _ SBO15 SBO14 SBO13 SBO12 SBZ11 SBZ10 SBZ9 SBZ8 0 0 0 0 _ _ _ _ ->
      decode_cond w (fun condition => MSRreg R_ condition (bits n19 n16 w) (regnum_from_bit n0 w))
    (*4.1.40 - MUL*)
    | word28 0 0 0 0 0 0 0 S_ _ _ _ _ SBZ15 SBZ14 SBZ13 SBZ12 _ _ _ _ 1 0 0 1 _ _ _ _ ->
      decode_cond w (fun condition => MUL S_ condition (regnum_from_bit n16 w) (regnum_from_bit n0 w) (regnum_from_bit n8 w))
    (*4.1.25 - LDRBT*)
    | word28 0 1 I_ 0 U_ 1 1 1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ->
      decode_cond_mode decode_addr_mode2 w (fun add_mode condition => LDRBT add_mode condition (regnum_from_bit n12 w))
    (*4.1.31 - LDRT*)
    | word28 0 1 I_ 0 U_ 0 1 1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ->
      decode_cond_mode decode_addr_mode2 w (fun add_mode condition => LDRT add_mode condition (regnum_from_bit n12 w))
    (*4.1.101 - STRBT*)
    | word28 0 1 I_ 0 U_ 1 1 0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ->
      decode_cond_mode decode_addr_mode2 w (fun add_mode condition => STRBT add_mode condition (regnum_from_bit n12 w))
    (*4.1.105 - STRT*)
    | word28 0 1 I_ 0 U_ 0 1 0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ->
      decode_cond_mode decode_addr_mode2 w (fun add_mode condition => STRT add_mode condition (regnum_from_bit n12 w))
    (*4.1.26 - LDRD*)
    | word28 0 0 0 P_ U_ I_ W_ 0 _ _ _ _ _ _ _ _ _ _ _ _ 1 1 0 1 _ _ _ _ ->
      decode_cond_mode decode_addr_mode3 w (fun add_mode condition => LDRD add_mode condition (regnum_from_bit n12 w))
    (*4.1.28 - LDRH*)
    | word28 0 0 0 P_ U_ I_ W_ 1 _ _ _ _ _ _ _ _ _ _ _ _ 1 0 1 1 _ _ _ _ ->
      decode_cond_mode decode_addr_mode3 w (fun add_mode condition => LDRH add_mode condition (regnum_from_bit n12 w))
    (*4.1.29 - LDRSB*)
    | word28 0 0 0 P_ U_ I_ W_ 1 _ _ _ _ _ _ _ _ _ _ _ _ 1 1 0 1 _ _ _ _ ->
      decode_cond_mode decode_addr_mode3 w (fun add_mode condition => LDRSB add_mode condition (regnum_from_bit n12 w))
    (*4.1.30 - LDRSH*)
    | word28 0 0 0 P_ U_ I_ W_ 1 _ _ _ _ _ _ _ _ _ _ _ _ 1 1 1 1 _ _ _ _ ->
      decode_cond_mode decode_addr_mode3 w (fun add_mode condition => LDRSH add_mode condition (regnum_from_bit n12 w))
    (*4.1.102 - STRD*)
    | word28 0 0 0 P_ U_ I_ W_ 0 _ _ _ _ _ _ _ _ _ _ _ _ 1 1 1 1 _ _ _ _ ->
      decode_cond_mode decode_addr_mode3 w (fun add_mode condition => STRD add_mode condition (regnum_from_bit n12 w))
    (*4.1.104 - STRH*)
    | word28 0 0 0 P_ U_ I_ W_ 0 _ _ _ _ _ _ _ _ _ _ _ _ 1 0 1 1 _ _ _ _ ->
      decode_cond_mode decode_addr_mode3 w (fun add_mode condition => STRH add_mode condition (regnum_from_bit n12 w))
    (*4.1.38 - MRS*)
    | word28 0 0 0 1 0 R_ 0 0 SBO19 SBO18 SBO17 SBO16 _ _ _ _ SBZ11 SBZ10 SBZ9 SBZ8 SBZ7 SBZ6 SBZ5 SBZ4 SBZ3 SBZ2 SBZ1 SBZ0 ->
      decode_cond w (fun condition => MRS R_ condition (regnum_from_bit n12 w))
    (*4.1.2 - ADC*)
    | word28 0 0 I_ 0 1 0 1 S_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ->
      decode_cond_mode decode_addr_mode1 w (fun add_mode condition => ADC add_mode S_ condition (regnum_from_bit n12 w) (regnum_from_bit n16 w))
    (*4.1.3 - ADD*)
    | word28 0 0 I_ 0 1 0 0 S_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ->
      decode_cond_mode decode_addr_mode1 w (fun add_mode condition => ADD add_mode S_ condition (regnum_from_bit n12 w) (regnum_from_bit n16 w))
    (*4.1.4 - AND*)
    | word28 0 0 I_ 0 0 0 0 S_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ->
      decode_cond_mode decode_addr_mode1 w (fun add_mode condition => AND add_mode S_ condition (regnum_from_bit n12 w) (regnum_from_bit n16 w))
    (*4.1.6 - BIC*)
    | word28 0 0 I_ 1 1 1 0 S_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ->
      decode_cond_mode decode_addr_mode1 w (fun add_mode condition => BIC add_mode S_ condition (regnum_from_bit n12 w) (regnum_from_bit n16 w))
    (*4.1.14 - CMN*)
    | word28 0 0 I_ 1 0 1 1 1 _ _ _ _ SBZ15 SBZ14 SBZ13 SBZ12 _ _ _ _ _ _ _ _ _ _ _ _ ->
      decode_cond_mode decode_addr_mode1 w (fun add_mode condition => CMN add_mode condition (regnum_from_bit n16 w))
    (*4.1.15 - CMP*)
    | word28 0 0 I_ 1 0 1 0 1 _ _ _ _ SBZ15 SBZ14 SBZ13 SBZ12 _ _ _ _ _ _ _ _ _ _ _ _ ->
      decode_cond_mode decode_addr_mode1 w (fun add_mode condition => CMP add_mode condition (regnum_from_bit n16 w))
    (*4.1.18 - EOR*)
    | word28 0 0 I_ 0 0 0 1 S_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ->
      decode_cond_mode decode_addr_mode1 w (fun add_mode condition => EOR add_mode S_ condition (regnum_from_bit n12 w) (regnum_from_bit n16 w))
    (*4.1.19 - LDC*)
    | word28 1 1 0 P_ U_ N_ W_ 1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ->
      decode_cond_mode decode_addr_mode5 w (fun add_mode condition => LDC add_mode condition (bits n11 n8 w))
    (*4.1.20 - LDM (1)*)
    | word28 1 0 0 P_ U_ 0 W_ 1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ->
      decode_cond_mode decode_addr_mode4 w (fun add_mode condition => LDM1 add_mode condition (bits n15 n0 w))
    (*4.1.21 - LDM (2)*)
    | word28 1 0 0 P_ U_ 1 0 1 _ _ _ _ 0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ->
      decode_cond_mode decode_addr_mode4 w (fun add_mode condition => LDM2 add_mode condition (bits n14 n0 w))
    (*4.1.22 - LDM (3)*)
    | word28 1 0 0 P_ U_ 1 W_ 1 _ _ _ _ 1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ->
      decode_cond_mode decode_addr_mode4 w (fun add_mode condition => LDM3 add_mode condition (bits n14 n0 w))
    (*4.1.23 - LDR*)
    | word28 0 1 I_ P_ U_ 0 W_ 1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ->
      decode_cond_mode decode_addr_mode2 w (fun add_mode condition => LDR add_mode condition (regnum_from_bit n12 w))
    (*4.1.24 - LDRB*)
    | word28 0 1 I_ P_ U_ 1 W_ 1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ->
      decode_cond_mode decode_addr_mode2 w (fun add_mode condition => LDRB add_mode condition (regnum_from_bit n12 w))
    (*4.1.35 - MOV*)
    | word28 0 0 I_ 1 1 0 1 S_ SBZ19 SBZ18 SBZ17 SBZ16 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ->
      decode_cond_mode decode_addr_mode1 w (fun add_mode condition => MOV add_mode S_ condition (regnum_from_bit n12 w))
    (*4.1.41 - MVN*)
    | word28 0 0 I_ 1 1 1 1 S_ SBZ19 SBZ18 SBZ17 SBZ16 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ->
      decode_cond_mode decode_addr_mode1 w (fun add_mode condition => MVN add_mode S_ condition (regnum_from_bit n12 w))
    (*4.1.42 - ORR*)
    | word28 0 0 I_ 1 1 0 0 S_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ->
      decode_cond_mode decode_addr_mode1 w (fun add_mode condition => ORR add_mode S_ condition (regnum_from_bit n12 w) (regnum_from_bit n16 w))
    (*4.1.60 - RSB*)
    | word28 0 0 I_ 0 0 1 1 S_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ->
      decode_cond_mode decode_addr_mode1 w (fun add_mode condition => RSB add_mode S_ condition (regnum_from_bit n12 w) (regnum_from_bit n16 w))
    (*4.1.61 - RSC*)
    | word28 0 0 I_ 0 1 1 1 S_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ->
      decode_cond_mode decode_addr_mode1 w (fun add_mode condition => RSC add_mode S_ condition (regnum_from_bit n12 w) (regnum_from_bit n16 w))
    (*4.1.65 - SBC*)
    | word28 0 0 I_ 0 1 1 0 S_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ->
      decode_cond_mode decode_addr_mode1 w (fun add_mode condition => SBC add_mode S_ condition (regnum_from_bit n12 w) (regnum_from_bit n16 w))
    (*4.1.96 - STC*)
    | word28 1 1 0 P_ U_ N_ W_ 0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ->
      decode_cond_mode decode_addr_mode5 w (fun add_mode condition => STC add_mode condition (bits n11 n8 w))
    (*4.1.97 - STM (1)*)
    | word28 1 0 0 P_ U_ 0 W_ 0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ->
      decode_cond_mode decode_addr_mode4 w (fun add_mode condition => STM1 add_mode condition (bits n15 n0 w))
    (*4.1.98 - STM (2)*)
    | word28 1 0 0 P_ U_ 1 0 0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ->
      decode_cond_mode decode_addr_mode4 w (fun add_mode condition => STM2 add_mode condition (bits n15 n0 w))
    (*4.1.99 - STR*)
    | word28 0 1 I_ P_ U_ 0 W_ 0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ->
      decode_cond_mode decode_addr_mode2 w (fun add_mode condition => STR add_mode condition (regnum_from_bit n12 w))
    (*4.1.100 - STRB*)
    | word28 0 1 I_ P_ U_ 1 W_ 0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ->
      decode_cond_mode decode_addr_mode2 w (fun add_mode condition => STRB add_mode condition (regnum_from_bit n12 w))
    (*4.1.106 - SUB*)
    | word28 0 0 I_ 0 0 1 0 S_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ->
      decode_cond_mode decode_addr_mode1 w (fun add_mode condition => SUB add_mode S_ condition (regnum_from_bit n12 w) (regnum_from_bit n16 w))
    (*4.1.116 - TEQ*)
    | word28 0 0 I_ 1 0 0 1 1 _ _ _ _ SBZ15 SBZ14 SBZ13 SBZ12 _ _ _ _ _ _ _ _ _ _ _ _ ->
      decode_cond_mode decode_addr_mode1 w (fun add_mode condition => TEQ add_mode condition (regnum_from_bit n16 w))
    (*4.1.117 - TST*)
    | word28 0 0 I_ 1 0 0 0 1 _ _ _ _ SBZ15 SBZ14 SBZ13 SBZ12 _ _ _ _ _ _ _ _ _ _ _ _ ->
      decode_cond_mode decode_addr_mode1 w (fun add_mode condition => TST add_mode condition (regnum_from_bit n16 w))
    | _ => DecUndefined inst
;;

let decode (w : word) : decoder_result inst :=
  match w32_of_word w with
    | word32 1 1 1 1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      decode_unconditional w
    | _ => decode_conditional w
  ;;
