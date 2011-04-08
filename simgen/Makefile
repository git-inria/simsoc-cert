# SimSoC-Cert, a toolkit for generating certified processor simulators
# See the COPYRIGHTS and LICENSE files.

DIR := ..

include $(DIR)/Makefile.common

TARGETS := main

default: patch-extraction $(TARGETS)

$(TARGETS): FORCE
	$(SHOW) ocamlbuild simgen/$@
	$(HIDE) $(OCAMLBUILD) simgen/$@.d.byte simgen/$@.native

.PHONY: patch-extraction

patch-extraction: extraction
	sed -i 's/= Vector.to_list n/v0 = Vector.to_list n v0/' extraction/RawCoq_Csyntax.ml

extraction.v: RawCoq_Csyntax.vo

clean::
	rm -f $(TARGETS) RawCoq_Csyntax.vo
