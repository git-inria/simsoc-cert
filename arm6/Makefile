# SimSoC-Cert, a toolkit for generating certified processor simulators
# See the COPYRIGHTS and LICENSE files.

DIR := ..

include $(DIR)/Makefile.common

default: arm6.pc arm6.dec arm6.syntax

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
	cp -f $< $@ && patch $@ < arm6inst.patch

arm6dec.txt: arm6.txt arm6dec.patch
	cp -f $< $@ && patch $@ < arm6dec.patch

arm6syntax.txt: arm6.txt arm6syntax.patch
	cp -f $< $@ && patch $@ < arm6syntax.patch

clean::
	rm -f arm6inst.txt arm6dec.txt arm6syntax.txt \
		arm6inst.txt.orig arm6dec.txt.orig arm6syntax.txt.orig

arm6patched.txt: arm6.txt arm6patch.ed
	cp -f $< $@ && ed -s $@ < arm6patch.ed

clean::
	rm -f arm6patched.txt

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

.PHONY: patch

patch: arm6.txt arm6patched.txt
	-diff -e $+ > arm6patch.ed; echo w >> arm6patch.ed

###########################################################################
# parsing

.DELETE_ON_ERROR: arm6.pc

arm6.pc: arm6patched.txt parsing/keepoper parsing/oneline_expr \
		parsing/preproc_pseudo.sh parsing/indentation
	$(SHOW) generate $@ from $<
	$(HIDE) cat $< | parsing/keepoper | parsing/oneline_expr \
		| parsing/preproc_pseudo.sh | parsing/indentation > $@

.DELETE_ON_ERROR: arm6.dec

arm6.dec: arm6patched.txt parsing/keepbincode parsing/parsebincode
	$(SHOW) generate $@ from $<
	$(HIDE) cat $< | parsing/keepbincode | parsing/parsebincode > $@

.DELETE_ON_ERROR: arm6.syntax

arm6.syntax: arm6patched.txt parsing/keepsyntax parsing/parsesyntax \
		parsing/blanks_syntax.sh
	$(SHOW) generate $@ from $<
	$(HIDE) cat $< | parsing/keepsyntax | parsing/blanks_syntax.sh \
		| parsing/parsesyntax > $@

ARM6_PARSING := indentation keepbincode keepoper oneline_expr parsebincode \
		keepsyntax parsesyntax

$(ARM6_PARSING:%=parsing/%): FORCE
	$(MAKE) -C $(DIR)/arm6/parsing $(@:parsing/%=%)

clean::
	rm -f arm6.pc arm6.dec arm6.syntax
