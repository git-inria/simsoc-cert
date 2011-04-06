# SimSoC-Cert, a toolkit for generating certified processor simulators
# See the COPYRIGHTS and LICENSE files.

DIR := .

include $(DIR)/Makefile.common

default: simgen

TARGETS := arm6 sh4

.PHONY: simgen $(TARGETS)
simgen $(TARGETS):
	$(MAKE) -C $@

SUBDIRS := simgen $(TARGETS) coq tools

clean::
	ocamlbuild -clean
	@for d in $(SUBDIRS); do make -C $$d $@; done
