# SimSoC-Cert, a toolkit for generating certified processor simulators
# See the COPYRIGHTS and LICENSE files.

DIR := ../..

include $(DIR)/Makefile.common

default:
	$(SHOW) ocamlbuild tools/dependot/dependot
	$(HIDE) $(OCAMLBUILD) tools/dependot/dependot.d.byte tools/dependot/dependot.native

.PHONY: check

check: default exemple.dot
	cmp exemple.dot exemple-ref.dot

%.dot: %.dep
	cat $< | ./dependot > $@

%.ps: %.dep
	cat $< | ./dependot | dot -Tps > $@

clean::
	rm -f dependot exemple.dot exemple.ps
