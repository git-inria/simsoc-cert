# SimSoC-Cert, a toolkit for generating certified processor simulators
# See the COPYRIGHTS and LICENSE files.

DIR := ../../../..

include $(DIR)/Makefile.common

TARGETS := instr

default: $(TARGETS)

$(TARGETS): FORCE
	$(SHOW) ocamlbuild devel/tuong/sh4/parsing/$@
	$(HIDE) $(OCAMLBUILD) -use-ocamlfind devel/tuong/sh4/parsing/$@.d.byte devel/tuong/sh4/parsing/$@.native

clean::
	rm -f $(TARGETS)
