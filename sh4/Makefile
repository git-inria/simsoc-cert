# SimSoC-Cert, a toolkit for generating certified processor simulators
# See the COPYRIGHTS and LICENSE files.

DIR := ..

include $(DIR)/Makefile.common

default: sh4.dat

SUBDIRS := parsing coq test

clean::
	@for d in $(SUBDIRS); do make -C $$d $@; done

###########################################################################
# file decompression

.PRECIOUS: sh4.txt

sh4.txt: sh4.txt.gz
	gunzip -c $< > $@

clean::
	rm -f sh4.txt

###########################################################################
# creation of sh4.txt.gz

.PHONY: pdftotext

pdftotext: sh4.pdf
	pdftotext -layout $< sh4.txt && gunzip sh4.txt

###########################################################################
# patch application

sh4inst.txt: sh4.txt sh4.patch
	patch $+ -o $@

clean::
	rm -f sh4inst.txt

###########################################################################
# patch update

.PHONY: patch-inst

patch-inst: sh4.txt sh4inst.txt
	-diff -u $+ > sh4.patch

###########################################################################
# parsing

.DELETE_ON_ERROR: sh4.dat

sh4.dat: sh4inst.txt parsing/instr
	parsing/instr < $< > $@

parsing/instr: FORCE
	$(MAKE) -C parsing instr

clean::
	rm -f sh4.dat
