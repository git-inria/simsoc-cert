# SimSoC-Cert, a Coq library on processor architectures for embedded systems.
# See the COPYRIGHTS and LICENSE files.

targ = keepoper indentation oneline_expr ARMv6.txt ARMv6.txt.orig operV6.txt indentV6.txt

all : $(targ)

clean :
	rm -f *.cm* *.o *~ $(targ)

# Usage : update ARMv6.txt to the desired contents, then make patch
# The purpose of "|| echo..." is to enforce an exit status to 0 (else weird make msg)
# FIXME (msg JF-> Fred) : idem pour indentV6.txt.patch.positif ? Sauf qu'ils devront disparaitre ?
# New version (15/12 00:55) : patch < indentV6.txt.patch.positif
#  -> all hunks failed
#  -> remove the use of indentV6.txt.patch.positif
#  -> FIXME : svn remove indentV6.txt.patch.positif
patch :
	diff -u ARMv6.txt.orig ARMv6.txt > ARMv6.txt.patch || echo ARMv6.txt.patch generated

keepoper : keepoper.ml
	ocamlopt -pp camlp4o $< -o $@

indentation : indentation.ml
	ocamlopt -pp camlp4o $< -o $@

oneline_expr : oneline_expr.ml
	ocamlopt -pp camlp4o $< -o $@

ARMv6.txt.orig : 
	pdftotext -layout ../ARMv6.pdf $@

# some informal text after "assert" -> /* comment */
ARMv6.txt : ARMv6.txt.orig ARMv6.txt.patch
	cp -a $< $@
	patch < ARMv6.txt.patch

operV6.txt : keepoper ARMv6.txt
	./keepoper < ARMv6.txt > $@

indentV6.txt : indentation oneline_expr preproc_pseudo.sh operV6.txt
	cat operV6.txt | ./oneline_expr | ./preproc_pseudo.sh | ./indentation > $@

# indentV6.txt.orig
#	cp -a $< $@
#	patch < indentV6.txt.patch.positif
