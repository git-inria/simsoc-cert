# SimSoC-Cert, a toolkit for generating certified processor simulators
# See the COPYRIGHTS and LICENSE files.

DIR := ../../../..

include $(DIR)/Makefile.common

TARGETS := preproc_pseudo

default: $(TARGETS)

$(TARGETS): FORCE
	$(SHOW) ocamlbuild devel/tuong/sh4/patching/$@
	$(HIDE) $(OCAMLBUILD) -package batteries devel/tuong/sh4/patching/$@.d.byte devel/tuong/sh4/patching/$@.native

clean::
	rm -f $(TARGETS)
