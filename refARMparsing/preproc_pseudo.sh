#!/bin/sh

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
    -e 's|^\( *\)if \(.*\)\([0-9]\)$|\1if \2\3 then|' \
    -e 's|^\( *\)while \(.*\)|\1while \2 do|' \
    -e 's|^\( *\)for \(.*\);|\1for \2 do|' \
    -e 's|-\([A-Za-z]\)| \1|g' \
    -e 's|bit position|bit_position|' \
    -e 's|address of|address_of|' \
    -e 's|\[cp_num\]| cp_num |' \
    -e 's|is even numbered|is_even_numbered|' \
    -e 's|is not|is_not|' \
    -e 's|v5 and above|v5_and_above|' \
    -e 's|v4 and earlier|v4_and_earlier|' \
    -e 's|value from|value_from|' \
    -e 's|CPSR with|CPSR_with|' \
    -e 's|SUB ARCHITECTURE|SUB_ARCHITECTURE|' \
    -e 's|^\( *\)If |\1if |' \
    -e 's|Artihmetic|Arithmetic|' \
    -e 's|(diff4]|(diff4)|' \
    -e 's|) – |) - |'

