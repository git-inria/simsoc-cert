# SimSoC-Cert, a toolkit for generating certified processor simulators
# See the COPYRIGHTS and LICENSE files.

DIR := ../../../..

include $(DIR)/Makefile.common

TARGETS := instr

default: $(TARGETS)

$(TARGETS): FORCE
	$(SHOW) ocamlbuild devel/tuong/sh4/parsing_frontc/$@
	$(HIDE) $(OCAMLBUILD) -use-ocamlfind devel/tuong/sh4/parsing_frontc/$@.d.byte devel/tuong/sh4/parsing_frontc/$@.native

clean::
	rm -f $(TARGETS)
