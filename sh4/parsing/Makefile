# SimSoC-Cert, a toolkit for generating certified processor simulators
# See the COPYRIGHTS and LICENSE files.

DIR := ../..

include $(DIR)/Makefile.common

.PHONY: default clean

default: instr

instr:
	$(BUILD) sh4/parsing/$@

clean:
	rm -f instr
