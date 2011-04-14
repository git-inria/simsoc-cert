# SimSoC-Cert, a toolkit for generating certified processor simulators
# See the COPYRIGHTS and LICENSE files.

DIR := .

include $(DIR)/Makefile.common

default:
	$(MAKE) -C simgen

SUBDIRS := tools simgen coq arm6 sh4

clean::
	ocamlbuild -no-links -clean
	@for d in $(SUBDIRS); do make -C $$d $@; done
