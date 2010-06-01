# SimSoC-Cert, a Coq library on processor architectures for embedded systems.
# See the COPYRIGHTS and LICENSE files.

SUBDIRS := order_deps dependot

.PHONY: default clean $(SUBDIRS)

.SUFFIXES:

default: $(SUBDIRS)

$(SUBDIRS) $(TARGETS):
	@$(MAKE) -C $@

%:
	@rm -f *~
	@for d in $(SUBDIRS); do make -C $$d $*; done
