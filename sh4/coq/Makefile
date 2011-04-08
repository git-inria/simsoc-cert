# SimSoC-Cert, a toolkit for generating certified processor simulators
# See the COPYRIGHTS and LICENSE files.

GENFILES := Sh4_Inst.v Sh4_Dec.v

.PHONY: first

first: $(GENFILES) libcoq default

######################################################################
# compile Coq files

DIR := ../..

FILES := Message Config Functions Proc State Simul

VFILES := Sh4.v $(FILES:%=Sh4_%.v) $(GENFILES)

COQ_INCLUDES := -I $(DIR)/coq

include $(DIR)/Makefile.coq

######################################################################
# generate Coq files

.DELETE_ON_ERROR: $(GENFILES)

Sh4_Inst.v: ../sh4.dat build-simgen
	$(SIMGEN) -sh4 -ipc $< -ocoq-inst > $@

Sh4_Dec.v: ../sh4.dat build-simgen
	$(SIMGEN) -sh4 -idec $< -ocoq-dec > $@

../sh4.dat: FORCE
	$(MAKE) -C .. $(shell basename $@)

clean::
	rm -f $(GENFILES)

######################################################################
# extraction

extraction: first FORCE
	$(SHOW) ocamlbuild sh4/coq/extraction/Sh4_Simul
	$(HIDE) $(OCAMLBUILD) sh4/coq/extraction/Sh4_Simul.d.byte \
		sh4/coq/extraction/Sh4_Simul.native
