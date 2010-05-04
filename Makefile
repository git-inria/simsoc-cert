# SimSoC-Cert, a Coq library on processor architectures for embedded systems.
# See the COPYRIGHTS and LICENSE files.

.SUFFIXES:

SUBDIRS := refARMparsing pseudocode coq testgen
TARGETS := arm6

.PHONY: default clean $(SUBDIRS) $(TARGETS)

ifeq ($(VERBOSE),1)
  SHOW := @true
  HIDE :=
else
  SHOW := @echo
  HIDE := @
endif

.PRECIOUS:

default: $(SUBDIRS)

$(SUBDIRS):
	$(MAKE) -C $@
	@echo "do make [$(TARGETS)] to generate the simulator"

$(TARGETS):
	$(MAKE) -C $@

clean:
	rm -f *~
	for d in $(SUBDIRS); do make -C $$d clean; done

