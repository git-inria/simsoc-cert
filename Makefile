# SimSoC-Cert, a Coq library on processor architectures for embedded systems.
# See the COPYRIGHTS and LICENSE files.

SUBDIRS := refARMparsing pseudocode coq testgen

TARGETS := arm6

.PHONY: default clean all $(SUBDIRS) $(TARGETS)

.SUFFIXES:

default: $(SUBDIRS)
	@echo; echo "do make [$(TARGETS)] to generate the simulator"

all: default $(TARGETS)

$(SUBDIRS) $(TARGETS):
	@$(MAKE) -C $@

clean:
	rm -f *~
	@for d in $(SUBDIRS); do make -C $$d clean; done
