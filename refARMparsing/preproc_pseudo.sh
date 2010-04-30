#!/bin/sh

# this script does the following modifications:

# add semi-colons at the end of various expressions
# permute comments and semi-colons
# add missing "then" with some "if"
# add "do" after "while" and "for"
# replace dash by a space
# replace "is" by "==", and "is not" by "!="
# replace "== R15" by "== 15"
# remove "value" of a register
# replace some English expressions by a function call
# fix some typos
# inline some code
# replace a strange dash character by a usual dash


# WARNING: do not remove the last strange -e command !
# it is due to a strange dash character

sed \
    -e '/^ *[a-zA-Z][a-zA-Z0-9 _(\+)]* = /s|$|;|' \
    -e '/^ *[a-zA-Z][a-zA-Z0-9 _(\+)]*\[[:0-9a-zA-Z_ ,+]*] *= /s|$|;|' \
    -e '/^ *if [a-zA-Z][a-zA-Z0-9 _]* == [a-zA-Z0-9][a-zA-Z0-9 _]*  *then  *[a-zA-Z][]\[a-zA-Z0-9 _]* *= /s|$|;|' \
    -e '/^ *MemoryAccess *(/s|$|;|' \
    -e '/^ *MarkExclusiveLocal *(/s|$|;|' \
    -e '/^ *MarkExclusiveGlobal *(/s|$|;|' \
    -e '/^ *ClearExclusiveByAddress *(/s|$|;|' \
    -e '/^ *ClearExclusiveLocal *(/s|$|;|' \
    -e '/^ *send /s|$|;|' \
    -e '/^ *load /s|$|;|' \
    -e '/^ *Start /s|$|;|' \
    -e '/^ *UNPREDICTABLE/s|$|;|' \
    -e '/^ *Coprocessor/s|$|;|' \
    -e '/^ *assert /s|$|;|' \
    -e 's|\( *//.*\);$|;\1|' \
    -e 's|\( */\*.*\*/\);|;\1|' \
    -e 's|if (\(.*\))$|if (\1) then|' \
    -e 's|^\( *\)if \(.*\)\([0-9)]\)$|\1if \2\3 then|' \
    -e 's|^\( *\)while \(.*\)|\1while \2 do|' \
    -e 's|^\( *\)for \(.*\);|\1for \2 do|' \
    -e 's|-\([A-Za-z]\)| \1|g' \
    -e 's|R\(.*\) is even numbered|is_even(\1)|' \
    -e 's|R\(.*\) is R|\1 == |' \
    -e 's|R\(.*\) is not R|\1 != |' \
    -e 's|R\(.*\) == R|\1 == |' \
    -e 's|value to|to|' \
    -e 's|first value|first_value|' \
    -e 's|second value|second_value|' \
    -e 's|dependent operation|dependent_operation|g' \
    -e 's|Mask|Mask()|' \
    -e 's|CP15\(.*\)bit|CP15\1bit()|' \
    -e 's|v4 and earlier|v4_and_earlier()|' \
    -e 's|v5 and above|v5_and_above()|' \
    -e 's|architecture version 5 or above|v5_and_above()|' \
    -e 's|ARMv5 or above|v5_and_above()|' \
    -e 's|IMPLEMENTATION DEFINED CONDITION|IMPLEMENTATION_DEFINED_CONDITION()|g' \
    -e 's|SUB ARCHITECTURE DEFINED value|SUB_ARCHITECTURE_DEFINED_value()|g' \
    -e 's|high vectors configured|high_vectors_configured()|' \
    -e 's|(JE bit of Main Configuration register)|JE_bit_of_Main_Configuration_register()|' \
    -e 's|(CV bit of Jazelle OS Control register)|CV_bit_of_Jazelle_OS_Control_register()|' \
    -e 's|(Jazelle Extension accepts opcode at jpc)|Jazelle_Extension_accepts_opcode_at(jpc)|' \
    -e 's|address of BKPT instruction|address_of_current_instruction()|' \
    -e 's|address of the instruction after the BLX instruction|address_of_next_instruction()|' \
    -e 's|address of instruction after the BLX instruction|address_of_next_instruction()|' \
    -e 's|address of next instruction after the SWI instruction|address_of_next_instruction()|' \
    -e 's|address of the instruction after the branch instruction|address_of_next_instruction()|' \
    -e 's|CPSR with specified E bit modification|CPSR_with_specified_E_bit_modification()|' \
    -e 's|(not overridden by debug hardware)|not_overridden_by_debug_hardware()|' \
    -e "s|bit position of most significant'1' in Rm|bit_position_of_most_significant_1(Rm)|" \
    -e 's|Start opcode execution at jpc|Start_opcode_execution_at(jpc)|' \
    -e 's|8_bit_immediate|immed_8|' \
    -e 's|8_bit_word_offset|offset_8|' \
    -e 's|coprocessor\[|Coprocessor[|' \
    -e 's|^\( *\)If |\1if |' \
    -e 's|Artihmetic|Arithmetic|' \
    -e 's|(diff4]|(diff4)|' \
    -e 's|memory\[|Memory\[|' \
    -e 's|<shift_imm>|shift_imm|' \
    -e 's|See “Data processing operands - Rotate right with extend” on page A5-17|shifter_operand = (C Flag Logical_Shift_Left 31) OR (Rm Logical_Shift_Right 1); shifter_carry_out = Rm[0]|' \
    -e 's|opcode\[\(.*\)\]|opcode\1|' \
    -e 's|–|-|'
