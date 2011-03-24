# SimSoC-Cert, a Coq library on processor architectures for embedded systems.
# See the COPYRIGHTS and LICENSE files.

MAKEFLAGS := --no-print-directory

SUBDIRS := tools refARMparsing pseudocode coq testgen

TARGETS := arm6 sh4

.PHONY: default clean clean-all all $(SUBDIRS) $(TARGETS) extract test

.SUFFIXES:

default: $(SUBDIRS)
	@echo; echo "do [make $(TARGETS)] to generate the simulator"

all: default $(TARGETS) extract test

$(SUBDIRS) $(TARGETS) extract test:
	@$(MAKE) -C $@

config:
	@for d in coq; do make -C $$d $@; done

clean:
	rm -f *~
	ocamlbuild -clean
	rm -rf extract/tmp
	@for d in $(SUBDIRS); do make -C $$d $@; done

clean-all: clean
	@for d in $(TARGETS) extract test; do make -C $$d clean; done
