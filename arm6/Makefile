# SimSoC-Cert, a toolkit for generating certified processor simulators
# See the COPYRIGHTS and LICENSE files.

DIR := ..

include $(DIR)/Makefile.common

.PHONY: default clean patch-inst patch-dec patch-syntax testparsing \
	$(SIMGEN) libcoq

FILES := arm6inst.txt arm6inst.arm arm6inst.v \
	arm6exn.arm arm6exn.v \
	arm6dec.txt arm6dec.dat arm6syntax.dat \
	arm6dec.v arm6mldec.ml arm6test.elf

default: arm6inst.vo arm6syntax.dat arm6dec.vo arm6.vo \
	arm6mldec.ml #arm6exn.vo

clean:
	rm -f *.glob *.vo *.orig $(FILES) arm6.txt arm6syntax.txt

.PRECIOUS: arm6.txt $(FILES)

arm6.txt: arm6.txt.gz
	gunzip -c $< > $@

###########################################################################
# patch application

arm6inst.txt: arm6.txt arm6inst.patch
	cp -a $< $@ && patch $@ < arm6inst.patch

#arm6exn.txt: arm6.txt arm6exn.patch
#	cp -a $< $@ && patch $@ < arm6exn.patch

arm6dec.txt: arm6.txt arm6dec.patch
	cp -a $< $@ && patch $@ < arm6dec.patch

arm6syntax.txt: arm6.txt arm6syntax.patch
	cp -a $< $@ && patch $@ < arm6syntax.patch

###########################################################################
# update patches

patch-inst: arm6.txt arm6inst.txt
	diff -u $+ > arm6inst.patch || exit 0

patch-dec: arm6.txt arm6dec.txt
	diff -u $+ > arm6dec.patch || exit 0

patch-syntax: arm6.txt arm6syntax.txt
	diff -u $+ > arm6syntax.patch || exit 0

#patch-exn: arm6.txt arm6exn.txt
#	diff -u $+ > arm6exn.patch || exit 0

###########################################################################
# parsing

arm6inst.arm: arm6inst.txt parsing/keepoper parsing/oneline_expr \
		parsing/preproc_pseudo.sh parsing/indentation
	$(SHOW) generate $@ from $<
	$(HIDE) cat $< | parsing/keepoper | parsing/oneline_expr \
		| parsing/preproc_pseudo.sh | parsing/indentation > $@ \
		|| (rm -f $@; exit 1)

arm6exn.arm: arm6exn.txt parsing/preproc_pseudo.sh
	$(SHOW) generate $@ from $<
	$(HIDE) cat $< | parsing/preproc_pseudo.sh > $@ \
		|| (rm -f $@; exit 1)

arm6dec.dat: arm6dec.txt parsing/keepbincode parsing/parsebincode
	$(SHOW) generate $@ from $<
	$(HIDE) cat $< | parsing/keepbincode | parsing/parsebincode > $@ \
		|| (rm -f $@; exit 1)

arm6syntax.dat: arm6syntax.txt parsing/keepsyntax parsing/parsesyntax \
		parsing/blanks_syntax.sh
	$(SHOW) generate $@ from $<
	$(HIDE) cat $< | parsing/keepsyntax | parsing/blanks_syntax.sh \
		| parsing/parsesyntax > $@ \
		|| (rm -f $@; exit 1)

testparsing: arm6inst.arm arm6dec.dat arm6syntax.dat arm6syntax.txt
	md5sum arm6inst.arm.ref arm6inst.arm arm6dec.dat.ref arm6dec.dat \
		arm6syntax.dat.ref arm6syntax.dat
	diff arm6inst.arm.ref arm6inst.arm
	diff arm6dec.dat.ref arm6dec.dat
	diff arm6syntax.dat.ref arm6syntax.dat

###########################################################################
# file generation

arm6inst.v: arm6inst.arm $(SIMGEN)
	$(SHOW) $(SIMGEN) -ipc $< -ocoq-inst > $@
	$(HIDE) $(SIMGEN) -ipc $< -ocoq-inst > $@ || (rm -f $@; exit 1)

arm6exn.v: arm6exn.arm $(SIMGEN)
	$(SHOW) $(SIMGEN) -ipc $< -ocoq-inst > $@
	$(HIDE) $(SIMGEN) -ipc $< -ocoq-inst > $@ || (rm -f $@; exit 1)

arm6dec.v: arm6dec.dat $(SIMGEN)
	$(SHOW) $(SIMGEN) -idec $< -ocoq-dec > $@
	$(HIDE) $(SIMGEN) -idec $< -ocoq-dec > $@ || (rm -f $@; exit 1)

arm6mldec.ml: arm6dec.dat $(SIMGEN)
	$(SHOW) $(SIMGEN) -idec $< -oml-dec > $@
	$(HIDE) $(SIMGEN) -idec $< -oml-dec > $@ || (rm -f $@; exit 1)

arm6test.bin: arm6dec.dat $(SIMGEN)
	$(SHOW) $(SIMGEN) -idec $< -otest > $@
	$(HIDE) $(SIMGEN) -idec $< -otest > $@ || (rm -f $@; exit 1)

%.vo: %.v libcoq
	$(SHOW) coqc $<
	$(HIDE) coqc -q -I $(DIR)/compcert/lib -I $(DIR)/coq -I $(DIR)/arm6/coq $<

%inst.cpp: %inst.arm $(SIMGEN)
	$(SIMGEN) -ipc $< -ocpp > $@

%exn.cpp: %exn.arm $(SIMGEN)
	$(SIMGEN) -ipc $< -ocpp > $@

%dec.cpp: %dec.dat $(SIMGEN)
	$(SIMGEN) -idec $< -ocpp > $@

parsing/keepoper parsing/oneline_expr parsing/keepsyntax parsing/parsesyntax \
	parsing/keepbincode parsing/parsebincode parsing/indentation:
	$(MAKE) -C parsing `basename $@`

$(SIMGEN):
	$(MAKE) -C $(DIR)/simgen

libcoq:
	$(MAKE) -C $(DIR)/coq -C $(DIR)/arm6/coq
