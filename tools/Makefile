# SimSoC-Cert, a toolkit for generating certified processor simulators
# See the COPYRIGHTS and LICENSE files.

SUBDIRS := bin2elf dependot

.PHONY: default clean $(SUBDIRS)

default: $(SUBDIRS)

$(SUBDIRS):
	$(MAKE) -C $@

clean:
	@for d in $(SUBDIRS); do make -C $$d $@; done
