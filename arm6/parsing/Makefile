# SimSoC-Cert, a toolkit for generating certified processor simulators
# See the COPYRIGHTS and LICENSE files.

DIR := ../..

include $(DIR)/Makefile.common

TARGETS := keepoper indentation oneline_expr keepbincode parsebincode \
	keepsyntax parsesyntax convert_syntax

default: $(TARGETS)

$(TARGETS):
	$(SHOW) OCAMLBUILD $@
	$(HIDE) cd $(DIR) && \
	$(OCAMLBUILD) $@.d.byte $@.native $@_finalize

clean:
	rm -f $(TARGETS)

.PHONY: default clean testoper testbincode testsyntax

# for debug:

testoper:
	./keepoper < arm6inst.txt > resu_keepoper

testbincode:
	./keepbincode < arm6dec.txt > resu_keepbincode

testsyntax:
	./keepsyntax < arm6syntax.txt > resu_keepsyntax
