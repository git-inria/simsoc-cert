# SimSoC-Cert, a toolkit for generating certified processor simulators
# See the COPYRIGHTS and LICENSE files.

DIR := ../..

include $(DIR)/Makefile.common

TARGETS := keepoper indentation oneline_expr keepbincode parsebincode \
	keepsyntax parsesyntax convert_syntax

default: $(TARGETS)

$(TARGETS): FORCE
	$(BUILD) arm6/parsing/$@

clean::
	rm -f $(TARGETS)
