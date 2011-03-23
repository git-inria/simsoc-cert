# SimSoC-Cert, a Coq library on processor architectures for embedded systems.
# See the COPYRIGHTS and LICENSE files.

TARGETS = keepoper indentation oneline_expr keepbincode parsebincode keepsyntax parsesyntax convert_syntax

ifeq ($(VERBOSE),1)
  SHOW := @true
  HIDE :=
else
  SHOW := @echo
  HIDE := @
endif

default: 
	$(SHOW) OCAMLBUILD $(TARGETS)
	$(HIDE) cd .. && \
	ocamlbuild -j 2 -no-hygiene -no-links \
		$(patsubst %,refARMparsing/%.native, $(TARGETS)) \
		$(patsubst %,refARMparsing/%_finalize, $(TARGETS))

clean:
	rm -f *~ $(TARGETS)

testoper:
	./keepoper < arm6inst.txt > resu_keepoper

testbincode:
	./keepbincode < arm6dec.txt > resu_keepbincode

testsyntax:
	./keepsyntax < arm6syntax.txt > resu_keepsyntax
