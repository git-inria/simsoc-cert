# SimSoC-Cert, a toolkit for generating certified processor simulators
# See the COPYRIGHTS and LICENSE files.

GENFILES := Arm6_Inst.v Arm6_Dec.v

.PHONY: coq

coq: libcoq $(GENFILES) default

######################################################################
# compile Coq files

DIR := ../..

FILES := Message Config Functions SCC Exception Proc State Simul

VFILES := Arm6.v $(FILES:%=Arm6_%.v) $(GENFILES)

COQ_INCLUDES := -I $(DIR)/coq

include $(DIR)/Makefile.coq

######################################################################
# generate Coq files

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
# extraction

ocaml: extraction-libcoq extraction
	$(SHOW) ocamlbuild arm6/coq/extraction/Arm6_Simul
	$(HIDE) $(OCAMLBUILD) arm6/coq/extraction/Arm6_Simul.d.byte \
		arm6/coq/extraction/Arm6_Simul.native

extraction.v: coq
