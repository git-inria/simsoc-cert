# SimSoC-Cert, a toolkit for generating certified processor simulators
# See the COPYRIGHTS and LICENSE files.

DIR := ../..

######################################################################
# first generate arm6inst.v and arm6dec.v

GENFILES := arm6inst.v arm6dec.v

.PHONY: first

first: $(GENFILES) default

.DELETE_ON_ERROR: $(GENFILES)

arm6inst.v: ../arm6inst.arm build-simgen
	$(SIMGEN) -ipc $< -ocoq-inst > $@

arm6dec.v: ../arm6dec.dat build-simgen
	$(SIMGEN) -idec $< -ocoq-dec > $@

../arm6inst.arm ../arm6dec.dat: FORCE
	$(MAKE) -C .. $(shell basename $@)

clean::
	rm -f $(GENFILES)

######################################################################
# then, compile all coq files

FILES := Message Config Functions SCC Exception Proc State

VFILES := Arm.v $(FILES:%=Arm_%.v) $(GENFILES) Arm6_Simul.v

INCLUDES := -I $(DIR)/compcert/lib -I $(DIR)/coq

include $(DIR)/Makefile.coq
