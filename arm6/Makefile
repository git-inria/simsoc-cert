# SimSoC-Cert, a toolkit for generating certified processor simulators
# See the COPYRIGHTS and LICENSE files.

DIR := ..

include $(DIR)/Makefile.common

FILES := arm6inst.txt arm6inst.arm arm6inst.v \
	arm6exn.arm arm6exn.v \
	arm6dec.txt arm6dec.dat arm6syntax.dat \
	arm6dec.v arm6mldec.ml arm6test.elf

#default: arm6inst.vo arm6syntax.dat arm6dec.vo arm6.vo \
#	arm6mldec.ml extraction

default:

SUBDIRS := parsing simlight simlight2 test coq elf2coq

clean::
	rm -rf extraction *.glob *.vo *.orig $(FILES) arm6.txt arm6syntax.txt
	@for d in $(SUBDIRS); do make -C $$d $@; done

.PRECIOUS: arm6.txt $(FILES)

###########################################################################
# file decompression

arm6.txt: arm6.txt.gz
	gunzip -c $< > $@

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

arm6inst.arm: arm6inst.txt parsing/keepoper parsing/oneline_expr \
		parsing/preproc_pseudo.sh parsing/indentation
	$(SHOW) generate $@ from $<
	$(HIDE) cat $< | parsing/keepoper | parsing/oneline_expr \
		| parsing/preproc_pseudo.sh | parsing/indentation > $@

.DELETE_ON_ERROR: arm6exn.arm

arm6exn.arm: arm6exn.txt parsing/preproc_pseudo.sh
	$(SHOW) generate $@ from $<
	$(HIDE) cat $< | parsing/preproc_pseudo.sh > $@

.DELETE_ON_ERROR: arm6dec.dat

arm6dec.dat: arm6dec.txt parsing/keepbincode parsing/parsebincode
	$(SHOW) generate $@ from $<
	$(HIDE) cat $< | parsing/keepbincode | parsing/parsebincode > $@

.DELETE_ON_ERROR: arm6syntax.dat

arm6syntax.dat: arm6syntax.txt parsing/keepsyntax parsing/parsesyntax \
		parsing/blanks_syntax.sh
	$(SHOW) generate $@ from $<
	$(HIDE) cat $< | parsing/keepsyntax | parsing/blanks_syntax.sh \
		| parsing/parsesyntax > $@

parsing/keepoper parsing/oneline_expr parsing/keepsyntax parsing/parsesyntax \
	parsing/keepbincode parsing/parsebincode parsing/indentation:
	$(MAKE) -C parsing `basename $@`

.PHONY: testparsing
testparsing: arm6inst.arm arm6dec.dat arm6syntax.dat \
		arm6inst.arm.ref arm6dec.dat.ref arm6syntax.dat.ref
	md5sum arm6inst.arm.ref arm6inst.arm arm6dec.dat.ref arm6dec.dat \
		arm6syntax.dat.ref arm6syntax.dat
	diff arm6inst.arm.ref arm6inst.arm
	diff arm6dec.dat.ref arm6dec.dat
	diff arm6syntax.dat.ref arm6syntax.dat

###########################################################################
# file generation using simgen

.DELETE_ON_ERROR: arm6mldec.ml

arm6mldec.ml: arm6dec.dat build-simgen
	$(SIMGEN) -idec $< -oml-dec > $@

.DELETE_ON_ERROR: arm6test.bin

arm6test.bin: arm6dec.dat build-simgen
	$(SIMGEN) -idec $< -otest > $@

#.DELETE_ON_ERROR: arm6inst.cpp
#arm6inst.cpp: arm6inst.arm build-simgen
#	$(SIMGEN) -ipc $< -ocpp > $@

#.DELETE_ON_ERROR: arm6exn.cpp
#arm6exn.cpp: arm6exn.arm build-simgen
#	$(SIMGEN) -ipc $< -ocpp > $@

#.DELETE_ON_ERROR: arm6dec.cpp
#arm6dec.cpp: arm6dec.dat build-simgen
#	$(SIMGEN) -idec $< -ocpp > $@
