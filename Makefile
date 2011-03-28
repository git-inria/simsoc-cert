# SimSoC-Cert, a toolkit for generating certified processor simulators
# See the COPYRIGHTS and LICENSE files.

#MAKEFLAGS := --no-print-directory

SUBDIRS := tools refARMparsing pseudocode coq testgen

TARGETS := arm6 sh4

.PHONY: default clean all $(SUBDIRS) $(TARGETS) extract test

.SUFFIXES:

default: $(SUBDIRS)
	@echo; echo "do [make $(TARGETS)] to generate the simulator"

all: default $(TARGETS) extract test

$(SUBDIRS) $(TARGETS) extract test:
	@$(MAKE) -C $@

config:
	$(MAKE) -C coq $@

clean:
	ocamlbuild -clean
	@for d in $(SUBDIRS); do make -C $$d $@; done
