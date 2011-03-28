# SimSoC-Cert, a toolkit for generating certified processor simulators
# See the COPYRIGHTS and LICENSE files.

include ../Makefile.common

TARGETS = keepoper indentation oneline_expr keepbincode parsebincode \
	keepsyntax parsesyntax convert_syntax

default: 
	$(SHOW) OCAMLBUILD $(TARGETS)
	$(HIDE) cd .. && \
	$(OCAMLBUILD) \
		$(patsubst %,refARMparsing/%.native, $(TARGETS)) \
		$(patsubst %,refARMparsing/%_finalize, $(TARGETS))

clean:
	rm -f $(TARGETS)

# for debug:

testoper:
	./keepoper < arm6inst.txt > resu_keepoper

testbincode:
	./keepbincode < arm6dec.txt > resu_keepbincode

testsyntax:
	./keepsyntax < arm6syntax.txt > resu_keepsyntax
