# SimSoC-Cert, a Coq library on processor architectures for embedded systems.
# See the COPYRIGHTS and LICENSE files.

PROC := arm6

FILES := $(PROC)inst.txt $(PROC)inst.arm $(PROC)inst.v \
	$(PROC)exn.arm $(PROC)exn.v \
	$(PROC)dec.txt $(PROC)dec.dat $(PROC)syntax.dat $(PROC)dec.v $(PROC)test.elf

DIR := ../refARMparsing

GEN := ../pseudocode/main

.PHONY: default clean patch-inst patch-dec

.PRECIOUS: $(PROC).txt $(FILES)

default: $(PROC)inst.vo $(PROC)dec.vo $(PROC).vo #$(PROC)exn.vo
testrefARMparsing: $(PROC)inst.arm $(PROC)dec.dat $(PROC)syntax.dat $(PROC)syntax.txt
	md5sum $(PROC)inst.arm.ref $(PROC)inst.arm $(PROC)dec.dat.ref $(PROC)dec.dat $(PROC)syntax.txt.ref $(PROC)syntax.dat $(PROC)syntax.txt
	diff $(PROC)inst.arm.ref $(PROC)inst.arm
	diff $(PROC)dec.dat.ref $(PROC)dec.dat
	diff $(PROC)syntax.dat.ref $(PROC)syntax.dat
	diff $(PROC)syntax.txt.ref $(PROC)syntax.txt

%.txt: %.pdf
	pdftotext -layout $< $@

%inst.txt: %.txt %inst.patch
	cp -a $< $@; patch $@ < $*inst.patch

#%exn.txt: %.txt %exn.patch
#	cp -a $< $@; patch $@ < $*exn.patch

%dec.txt: %.txt %dec.patch
	cp -a $< $@; patch $@ < $*dec.patch

%syntax.txt: %.txt %syntax.patch
	cp -a $< $@; patch $@ < $*syntax.patch

%inst.arm: %inst.txt $(DIR)/keepoper $(DIR)/oneline_expr $(DIR)/preproc_pseudo.sh $(DIR)/indentation
	cat $< | $(DIR)/keepoper | $(DIR)/oneline_expr | $(DIR)/preproc_pseudo.sh | $(DIR)/indentation > $@ || (rm -f $@; exit 1)

%exn.arm: %exn.txt $(DIR)/preproc_pseudo.sh
	cat $< | $(DIR)/preproc_pseudo.sh > $@ || (rm -f $@; exit 1)

%dec.dat: %dec.txt $(DIR)/keepbincode $(DIR)/parsebincode
	cat $< | $(DIR)/keepbincode | $(DIR)/parsebincode > $@ || (rm -f $@; exit 1)

%syntax.dat: %syntax.txt $(DIR)/keepsyntax $(DIR)/parsesyntax
	cat $< | $(DIR)/keepsyntax | $(DIR)/parsesyntax > $@ || (rm -f $@; exit 1)

%inst.v: %inst.arm $(GEN)
	$(GEN) -ipc $< -ocoq-inst > $@ || (rm -f $@; exit 1)

%exn.v: %exn.arm $(GEN)
	$(GEN) -ipc $< -ocoq-inst > $@ || (rm -f $@; exit 1)

%dec.v: %dec.dat $(GEN)
	$(GEN) -idec $< -ocoq-dec > $@ || (rm -f $@; exit 1)

%test.bin: %dec.dat $(GEN)
	$(GEN) -idec $< -otest > $@ || (rm -f $@; exit 1)

%.vo: %.v
	time -p coqc -q -R ../coq SimSoCCert $<

%inst.cpp: %inst.arm $(GEN)
	$(GEN) -ipc $< -ocpp > $@

%exn.cpp: %exn.arm $(GEN)
	$(GEN) -ipc $< -ocpp > $@

%dec.cpp: %dec.dat $(GEN)
	$(GEN) -idec $< -ocpp > $@

clean:
	rm -f *~ *.glob *.vo $(FILES)

usage-patch-inst:
	echo update $(PROC)inst.txt to the desired contents, then make patch-inst

patch-inst:
	diff -u $(PROC).txt $(PROC)inst.txt > $(PROC)inst.patch || exit 0

usage-patch-dec:
	echo update $(PROC)dec.txt to the desired contents, then make patch-dec

patch-dec:
	diff -u $(PROC).txt $(PROC)dec.txt > $(PROC)dec.patch || exit 0

usage-patch-syntax:
	echo update $(PROC)syntax.txt to the desired contents, then make patch-syntax

patch-syntax:
	diff -u $(PROC).txt $(PROC)syntax.txt > $(PROC)syntax.patch || exit 0

usage-patch-exn:
	echo update $(PROC)exn.txt to the desired contents, then make patch-exn

#patch-exn:
#	diff -u $(PROC).txt $(PROC)exn.txt > $(PROC)exn.patch || exit 0
