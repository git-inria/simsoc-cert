# SimSoC-Cert, a Coq library on processor architectures for embedded systems.
# See the COPYRIGHTS and LICENSE files.

DIR := ..

include $(DIR)/Makefile.common

SIMGEN := $(DIR)/pseudocode/main

PROC := arm6

FILES := $(PROC)inst.txt $(PROC)inst.arm $(PROC)inst.v \
	$(PROC)exn.arm $(PROC)exn.v \
	$(PROC)dec.txt $(PROC)dec.dat $(PROC)syntax.dat \
	$(PROC)dec.v $(PROC)mldec.ml $(PROC)test.elf

default: $(PROC)inst.vo $(PROC)syntax.dat $(PROC)dec.vo $(PROC).vo \
	$(PROC)mldec.ml #$(PROC)exn.vo

clean:
	rm -f *.glob *.vo *.orig $(FILES) $(PROC).txt $(PROC)syntax.txt

.PHONY: default clean patch-inst patch-dec patch-syntax testparsing \
	$(SIMGEN) libcoq

.PRECIOUS: $(PROC).txt $(FILES)

%.txt: %.txt.gz
	gunzip -c $< > $@

###########################################################################
# patch application

%inst.txt: %.txt %inst.patch
	cp -a $< $@ && patch $@ < $*inst.patch

#%exn.txt: %.txt %exn.patch
#	cp -a $< $@ && patch $@ < $*exn.patch

%dec.txt: %.txt %dec.patch
	cp -a $< $@ && patch $@ < $*dec.patch

%syntax.txt: %.txt %syntax.patch
	cp -a $< $@ && patch $@ < $*syntax.patch

###########################################################################
# parsing

%inst.arm: %inst.txt parsing/keepoper parsing/oneline_expr parsing/preproc_pseudo.sh parsing/indentation
	$(SHOW) generate $@ from $<
	$(HIDE) cat $< | parsing/keepoper | parsing/oneline_expr | parsing/preproc_pseudo.sh | parsing/indentation > $@ || (rm -f $@; exit 1)

%exn.arm: %exn.txt parsing/preproc_pseudo.sh
	$(SHOW) generate $@ from $<
	$(HIDE) cat $< | parsing/preproc_pseudo.sh > $@ || (rm -f $@; exit 1)

%dec.dat: %dec.txt parsing/keepbincode parsing/parsebincode
	$(SHOW) generate $@ from $<
	$(HIDE) cat $< | parsing/keepbincode | parsing/parsebincode > $@ || (rm -f $@; exit 1)

%syntax.dat: %syntax.txt parsing/keepsyntax parsing/parsesyntax parsing/blanks_syntax.sh
	$(SHOW) PARSING $< $@
	$(HIDE) cat $< | parsing/keepsyntax | parsing/blanks_syntax.sh | parsing/parsesyntax > $@ || (rm -f $@; exit 1)

###########################################################################
# file generation

%inst.v: %inst.arm $(SIMGEN)
	$(SHOW) $(SIMGEN) -ipc $< -ocoq-inst > $@
	$(HIDE) $(SIMGEN) -ipc $< -ocoq-inst > $@ || (rm -f $@; exit 1)

%exn.v: %exn.arm $(SIMGEN)
	$(SHOW) $(SIMGEN) -ipc $< -ocoq-inst > $@
	$(HIDE) $(SIMGEN) -ipc $< -ocoq-inst > $@ || (rm -f $@; exit 1)

%dec.v: %dec.dat $(SIMGEN)
	$(SHOW) $(SIMGEN) -idec $< -ocoq-dec > $@
	$(HIDE) $(SIMGEN) -idec $< -ocoq-dec > $@ || (rm -f $@; exit 1)

%mldec.ml: %dec.dat $(SIMGEN)
	$(SHOW) $(SIMGEN) -idec $< -oml-dec > $@
	$(HIDE) $(SIMGEN) -idec $< -oml-dec > $@ || (rm -f $@; exit 1)

%test.bin: %dec.dat $(SIMGEN)
	$(SHOW) $(SIMGEN) -idec $< -otest > $@
	$(HIDE) $(SIMGEN) -idec $< -otest > $@ || (rm -f $@; exit 1)

%.vo: %.v libcoq
	$(SHOW) coqc $<
	$(HIDE) coqc -q -I $(DIR)/compcert/lib -R $(DIR)/coq SimSoCCert $<

%inst.cpp: %inst.arm $(SIMGEN)
	$(SIMGEN) -ipc $< -ocpp > $@

%exn.cpp: %exn.arm $(SIMGEN)
	$(SIMGEN) -ipc $< -ocpp > $@

%dec.cpp: %dec.dat $(SIMGEN)
	$(SIMGEN) -idec $< -ocpp > $@

parsing/keepoper parsing/oneline_expr parsing/keepsyntax parsing/parsesyntax parsing/keepbincode parsing/parsebincode parsing/indentation:
	$(MAKE) -C parsing `basename $@`

$(SIMGEN):
	$(MAKE) -C $(DIR)/pseudocode

libcoq:
	$(MAKE) -C $(DIR)/coq

###########################################################################
# update patches

patch-inst:
	diff -u $(PROC).txt $(PROC)inst.txt > $(PROC)inst.patch || exit 0

patch-dec:
	diff -u $(PROC).txt $(PROC)dec.txt > $(PROC)dec.patch || exit 0

patch-syntax:
	diff -u $(PROC).txt $(PROC)syntax.txt > $(PROC)syntax.patch || exit 0

#patch-exn:
#	diff -u $(PROC).txt $(PROC)exn.txt > $(PROC)exn.patch || exit 0

###########################################################################
# for debug

testparsing: $(PROC)inst.arm $(PROC)dec.dat $(PROC)syntax.dat \
	$(PROC)syntax.txt
	md5sum $(PROC)inst.arm.ref $(PROC)inst.arm $(PROC)dec.dat.ref $(PROC)dec.dat $(PROC)syntax.dat.ref $(PROC)syntax.dat
	diff $(PROC)inst.arm.ref $(PROC)inst.arm
	diff $(PROC)dec.dat.ref $(PROC)dec.dat
	diff $(PROC)syntax.dat.ref $(PROC)syntax.dat
