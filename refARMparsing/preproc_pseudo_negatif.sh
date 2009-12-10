#!/bin/sh

sed -e 's|$|;|' \
    -e 's|then;$|then|' \
    -e 's|then \([ ]*/\*.*\*/\);$|then \1|' \
    -e 's|else;$|else|' \
    -e 's|else \([ ]*/\*.*\*/\);$|else \1|' \
    -e 's|^\([ ]*/\*.*\*/\);|\1|' \
    -e 's|if (\(.*\));$|if (\1) then|' \
    -e 's|^\([ ]*\)if \(.*\)\([0-9]\);$|\1if \2\3 then|' \
    -e 's|bit position|bit_position|' \
    -e 's|address of|address_of|' \
    -e 's|\[cp_num\]| cp_num |' \
    -e 's|-\([A-Za-z]\)| \1|g' \
    -e 's|^\([ ]*\)while \(.*\);|\1while \2 do|' \
    -e 's|^\([ ]*\)for \(.*\);|\1for \2 do|' \
    -e 's|is even numbered|is_even_numbered|' \
    -e 's|is not|is_not|' \
    -e 's|v5 and above|v5_and_above|' \
    -e 's|v4 and earlier|v4_and_earlier|' \
    -e 's|value from|value_from|'
