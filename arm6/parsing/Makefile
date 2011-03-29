# SimSoC-Cert, a toolkit for generating certified processor simulators
# See the COPYRIGHTS and LICENSE files.

DIR := ../..

include $(DIR)/Makefile.common

TARGETS := keepoper indentation oneline_expr keepbincode parsebincode \
	keepsyntax parsesyntax convert_syntax

.PHONY: default clean testoper testbincode testsyntax

default: $(TARGETS)

$(TARGETS):
	$(BUILD) arm6/parsing/$@

clean:
	rm -f $(TARGETS)

testoper:
	./keepoper < arm6inst.txt > resu_keepoper

testbincode:
	./keepbincode < arm6dec.txt > resu_keepbincode

testsyntax:
	./keepsyntax < arm6syntax.txt > resu_keepsyntax
