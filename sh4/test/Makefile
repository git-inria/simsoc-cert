# SimSoC-Cert, a toolkit for generating certified processor simulators
# See the COPYRIGHTS and LICENSE files.

DIR := ../..

include $(DIR)/Makefile.common
OCAMLBUILD := ocamlbuild -j 2 -no-hygiene -no-links

.PHONY: default clean

default: main

main:
	$(SHOW) ocamlbuild $@
	$(HIDE) cd $(DIR) && \
		$(OCAMLBUILD) sh4/test/$@.d.byte # assembler error with native compilation

clean::
	rm -f main
