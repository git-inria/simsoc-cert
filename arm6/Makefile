# SimSoC-Cert, a Coq library on processor architectures for embedded systems.
# See the COPYRIGHTS and LICENSE files.

PROC := arm6

TARGETS := $(PROC:%=%inst) $(PROC:%=%dec)

DIR := ../refARMparsing

GEN := ../pseudocode/bin/main

.PHONY: default clean patch-inst patch-dec

.PRECIOUS: $(PROC:%=%.txt) $(TARGETS:%=%.txt) $(TARGETS:%=%.v) \
	$(PROC:%=%inst.arm) $(PROC:%=%dec.dat)

default: $(TARGETS:%=%.vo)

%.txt: %.pdf
	pdftotext -layout $< $@

%inst.txt: %.txt
	cp -a $< $@; patch $@ < $*inst.patch

%dec.txt: %.txt
	cp -a $< $@; patch $@ < $*dec.patch

%inst.arm: %inst.txt
	cat $< | $(DIR)/keepoper | $(DIR)/oneline_expr | $(DIR)/preproc_pseudo.sh | $(DIR)/indentation > $@

%dec.dat: %dec.txt
	cat $< | $(DIR)/keepbincode | $(DIR)/parsebincode > $@

%inst.v: %inst.arm
	$(GEN) -ipc $< -ocoq > $@ 

%dec.v: %dec.dat
	$(GEN) -idec $< -ocoq > $@ 

%.vo: %.v
	coqc -I ../coq $<

%inst.cpp: %inst.arm
	$(GEN) -ipc $< -ocpp > $@ 

%dec.cpp: %dec.dat
	$(GEN) -idec $< -ocpp > $@ 

clean:
	rm -f *~ *.v *.glob *.txt *.dat *.arm *.vo

# Usage: update $(PROC)inst.txt to the desired contents, then make patch-inst
patch-inst:
	-diff -u $(PROC).txt $(PROC)inst.txt > $(PROC)inst.patch

# Usage: update $(PROC)dec.txt to the desired contents, then make patch-dec
patch-dec:
	-diff -u $(PROC).txt $(PROC)dec.txt > $(PROC)dec.patch
