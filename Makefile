# SimSoC-Cert, a toolkit for generating certified processor simulators
# See the COPYRIGHTS and LICENSE files.

TARGETS := arm6 sh4

SUBDIRS := simgen $(TARGETS)

.PHONY: default clean simgen $(TARGETS)

default: simgen

$(TARGETS) simgen:
	$(MAKE) -C $@

clean:
	ocamlbuild -clean
	@for d in $(SUBDIRS); do make -C $$d $@; done
