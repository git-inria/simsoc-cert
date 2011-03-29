# SimSoC-Cert, a toolkit for generating certified processor simulators
# See the COPYRIGHTS and LICENSE files.

DIR := ../..

include $(DIR)/Makefile.common

.PHONY: default clean check

default: dependot

dependot:
	$(BUILD) tools/dependot/dependot

check: dependot exemple.dot
	cmp exemple.dot exemple-ref.dot

%.dot: %.dep
	cat $< | ./dependot > $@

%.ps: %.dep
	cat $< | ./dependot | dot -Tps > $@

clean:
	rm -f dependot exemple.dot exemple.ps
