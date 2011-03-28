# SimSoC-Cert, a toolkit for generating certified processor simulators
# See the COPYRIGHTS and LICENSE files.

TARGETS := arm6 sh4

SUBDIRS := pseudocode $(TARGETS)

.PHONY: default clean simgen $(TARGETS)

default: simgen

simgen:
	$(MAKE) -C pseudocode

$(TARGETS):
	$(MAKE) -C $@

clean:
	ocamlbuild -clean
	@for d in $(SUBDIRS); do make -C $$d $@; done
