# SimSoC-Cert, a toolkit for generating certified processor simulators
# See the COPYRIGHTS and LICENSE files.

DIR := ../..

GENFILES := Arm6_Inst.v Arm6_Dec.v

.PHONY: first

first: $(GENFILES) build-coq default

######################################################################
# generate Arm6_Inst.v and Arm6_Dec.v

.DELETE_ON_ERROR: $(GENFILES)

Arm6_Inst.v: ../arm6inst.arm build-simgen
	$(SIMGEN) -ipc $< -ocoq-inst > $@

Arm6_Dec.v: ../arm6dec.dat build-simgen
	$(SIMGEN) -idec $< -ocoq-dec > $@

../arm6inst.arm ../arm6dec.dat: FORCE
	$(MAKE) -C .. $(shell basename $@)

clean::
	rm -f $(GENFILES)

######################################################################
# compile all coq files

FILES := Message Config Functions SCC Exception Proc State Simul

VFILES := Arm6.v $(FILES:%=Arm6_%.v) $(GENFILES)

INCLUDES := -I $(DIR)/compcert/lib -I $(DIR)/coq

include $(DIR)/Makefile.coq

######################################################################
# extraction

extraction.v: Arm6_Simul.vo
