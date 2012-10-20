#!/bin/sh

# SimSoC-Cert, a Coq library on processor architectures for embedded systems.
# See the COPYRIGHTS and LICENSE files.

# this script does the following modifications:

# add semi-colons at the end of various expressions
# permute comments and semi-colons
# add missing "then" with some "if"
# add "do" after "while" and "for"
# replace "is" by "==", and "is not" by "!="
# replace "== Rn" by "== n"
# convert some constants into function calls

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
    -e '/^ *Start_/s|$|;|' \
    -e '/^ *UNPREDICTABLE/s|$|;|' \
    -e '/^ *Coprocessor/s|$|;|' \
    -e '/^ *assert /s|$|;|' \
    -e 's|\( *//.*\);$|;\1|' \
    -e 's|\( */\*.*\*/\);|;\1|' \
    -e 's|if (\(.*\))$|if (\1) then|' \
    -e 's|^\( *\)if \(.*\)\([0-9)]\)$|\1if \2\3 then|' \
    -e 's|^\( *\)while \(.*\)|\1while \2 do|' \
    -e 's|^\( *\)for \(.*\);|\1for \2 do|' \
    -e 's|R\(.*\) is even|is_even(\1)|' \
    -e 's|R\(.*\) is R|\1 == |' \
    -e 's|R\(.*\) is not R|\1 != |' \
    -e 's|R\(.*\) == R|\1 == |' \
    -e 's|Mask|Mask()|g' \
    -e 's|CP15\(.*\)bit|CP15\1bit()|' \
    -e 's|^\( *\)If |\1if |'
