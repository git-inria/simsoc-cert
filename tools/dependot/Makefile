# SimSoC-Cert, a toolkit for generating certified processor simulators
# See the COPYRIGHTS and LICENSE files.

DIR := ../..

include $(DIR)/Makefile.common

default:
	$(SHOW) ocamlbuild tools/dependot/dependot
	$(HIDE) $(OCAMLBUILD) tools/dependot/dependot.d.byte tools/dependot/dependot.native

.PHONY: check

check: exemple.dot
	cmp exemple.dot exemple-ref.dot

clean::
	rm -f dependot
