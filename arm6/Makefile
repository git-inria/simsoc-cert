# SimSoC-Cert, a toolkit for generating certified processor simulators
# See the COPYRIGHTS and LICENSE files.

DIR := ..

include $(DIR)/Makefile.common

default:
	@echo "do make in a subdirectory"

SUBDIRS := parsing simlight simlight2 coq elf2coq test

clean::
	@for d in $(SUBDIRS); do make -C $$d $@; done

###########################################################################
# file decompression

.PRECIOUS: arm6.txt

arm6.txt: arm6.txt.gz
	gunzip -c $< > $@

clean::
	rm -f arm6.txt

###########################################################################
# creation of arm6.txt.gz

.PHONY: pdftotext

pdftotext: arm6.pdf
	pdftotext -layout $< arm6.txt && gunzip arm6.txt

###########################################################################
# patch application

arm6inst.txt: arm6.txt arm6inst.patch
	cp -a $< $@ && patch $@ < arm6inst.patch

arm6dec.txt: arm6.txt arm6dec.patch
	cp -a $< $@ && patch $@ < arm6dec.patch

arm6syntax.txt: arm6.txt arm6syntax.patch
	cp -a $< $@ && patch $@ < arm6syntax.patch

clean::
	rm -f arm6inst.txt arm6dec.txt arm6syntax.txt \
		arm6inst.txt.orig arm6dec.txt.orig arm6syntax.txt.orig

###########################################################################
# update patches

.PHONY: patch-inst

patch-inst: arm6.txt arm6inst.txt
	-diff -u $+ > arm6inst.patch

.PHONY: patch-dec

patch-dec: arm6.txt arm6dec.txt
	-diff -u $+ > arm6dec.patch

.PHONY: patch-syntax

patch-syntax: arm6.txt arm6syntax.txt
	-diff -u $+ > arm6syntax.patch

###########################################################################
# parsing

.DELETE_ON_ERROR: arm6inst.arm

arm6inst.arm: arm6inst.txt build-keepoper build-oneline_expr \
		parsing/preproc_pseudo.sh build-indentation
	$(SHOW) generate $@ from $<
	$(HIDE) cat $< | parsing/keepoper | parsing/oneline_expr \
		| parsing/preproc_pseudo.sh | parsing/indentation > $@

.DELETE_ON_ERROR: arm6dec.dat

arm6dec.dat: arm6dec.txt build-keepbincode build-parsebincode
	$(SHOW) generate $@ from $<
	$(HIDE) cat $< | parsing/keepbincode | parsing/parsebincode > $@

.DELETE_ON_ERROR: arm6syntax.dat

arm6syntax.dat: arm6syntax.txt build-keepsyntax build-parsesyntax \
		parsing/blanks_syntax.sh
	$(SHOW) generate $@ from $<
	$(HIDE) cat $< | parsing/keepsyntax | parsing/blanks_syntax.sh \
		| parsing/parsesyntax > $@

clean::
	rm -f arm6inst.arm arm6dec.dat arm6syntax.dat
