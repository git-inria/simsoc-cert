# SimSoC-Cert, a Coq library on processor architectures for embedded systems.
# See the COPYRIGHTS and LICENSE files.

targ = keepoper indentation ARMv6.txt operV6.txt indentV6.txt

all : $(targ)

clean :
	rm -f *.cm* *.o *~ $(targ)

keepoper : keepoper.ml
	ocamlopt -pp camlp4o $< -o $@

indentation : indentation.ml
	ocamlopt -pp camlp4o $< -o $@

ARMv6.txt : 
	pdftotext -layout ../ARMv6.pdf ARMv6.txt

operV6.txt : keepoper ARMv6.txt
	./keepoper < ARMv6.txt > $@

indentV6.txt : indentation operV6.txt
	cat operV6.txt | sed -e 's|$$|;|' -e 's|then;$$|then|'  -e 's|then \([ ]*/\*.*\*/\);$$|then \1|' -e 's|else;$$|else|' -e 's|else \([ ]*/\*.*\*/\);$$|else \1|' -e 's|^\([ ]*/\*.*\*/\);|\1|' -e 's|if (\(.*\));$$|if (\1) then|' -e 's|^\([ ]*\)if \(.*\)\([0-9]\);$$|\1if \2\3 then|' -e 's|bit position|bit_position|' -e 's|address of|address_of|' -e 's|\[cp_num\]| cp_num |' -e 's|-\([A-Za-z]\)| \1|g' -e 's|^\([ ]*\)while \(.*\);|\1while \2 do|' -e 's|^\([ ]*\)for \(.*\);|\1for \2 do|' -e 's|is even numbered|is_even_numbered|' -e 's|is not|is_not|' -e 's|v5 and above|v5_and_above|' -e 's|v4 and earlier|v4_and_earlier|' -e 's|value from|value_from|' | ./indentation  > $@
