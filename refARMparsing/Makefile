# SimSoC-Cert, a Coq library on processor architectures for embedded systems.
# See the COPYRIGHTS and LICENSE files.

targ = keepoper indentation oneline_expr ARMv6.txt ARMv6.txt.orig operV6.txt indentV6.txt

all : $(targ)

clean :
	rm -f *.cm* *.o *~ $(targ)

keepoper : keepoper.ml
	ocamlopt -pp camlp4o $< -o $@

indentation : indentation.ml
	ocamlopt -pp camlp4o $< -o $@

oneline_expr : oneline_expr.ml
	ocamlopt -pp camlp4o $< -o $@

ARMv6.txt.orig : 
	pdftotext -layout ../ARMv6.pdf $@

# some informal text after "assert" -> /* comment */
ARMv6.txt : ARMv6.txt.orig
	cp -a $< $@
	patch < ARMv6.txt.patch

operV6.txt : keepoper ARMv6.txt
	./keepoper < ARMv6.txt > $@

indentV6.txt : indentation oneline_expr preproc_pseudo_negatif.sh operV6.txt indentV6.txt.patch
	cat operV6.txt | ./oneline_expr | ./preproc_pseudo_negatif.sh | ./indentation > $@
	patch indentV6.txt indentV6.txt.patch
