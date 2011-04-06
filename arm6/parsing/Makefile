# SimSoC-Cert, a toolkit for generating certified processor simulators
# See the COPYRIGHTS and LICENSE files.

DIR := ../..

include $(DIR)/Makefile.common

TARGETS := keepoper indentation oneline_expr keepbincode parsebincode \
	keepsyntax parsesyntax convert_syntax

default: $(TARGETS)

$(TARGETS):
	$(BUILD) arm6/parsing/$@

clean::
	rm -f $(TARGETS)

.PHONY: testoper
testoper:
	./keepoper < arm6inst.txt > resu_keepoper

.PHONY: testbincode
testbincode:
	./keepbincode < arm6dec.txt > resu_keepbincode

.PHONY: testsyntax
testsyntax:
	./keepsyntax < arm6syntax.txt > resu_keepsyntax
