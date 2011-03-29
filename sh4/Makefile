# SimSoC-Cert, a toolkit for generating certified processor simulators
# See the COPYRIGHTS and LICENSE files.

DIR := ..

include $(DIR)/Makefile.common

.PHONY: default parsing/instr all $(SIMGEN)

default: sh4.dat

clean:
	rm -f sh4.dat sh4inst.v sh4dec.v sh4inst.vo sh4dec.vo sh4.vo

sh4.txt: sh4.txt.gz
	gunzip -c $< > $@

###########################################################################
# patch application

sh4inst.txt: sh4.txt sh4.patch
	$(SHOW) PATCH sh4.patch $@
	$(HIDE) patch sh4.txt sh4.patch -o $@

###########################################################################
# patch update

patch-inst: sh4.txt sh4inst.txt
	diff -u $+ > sh4.patch || exit 0

###########################################################################
# parsing

sh4.dat: sh4inst.txt parsing/instr
	cat sh4inst.txt | parsing/instr > sh4.dat

parsing/instr:
	$(MAKE) -C parsing

###########################################################################
# file generation

sh4inst.v: sh4.dat $(SIMGEN)
	$(SHOW) $(SIMGEN) -sh4 -ipc $< -ocoq-inst > $@
	$(HIDE) $(SIMGEN) -sh4 -ipc $< -ocoq-inst > $@ || (rm -f $@; exit 1)

sh4dec.v: sh4.dat $(SIMGEN)
	$(SHOW) $(SIMGEN) -sh4 -idec $< -ocoq-dec > $@
	$(HIDE) $(SIMGEN) -sh4 -idec $< -ocoq-dec > $@ || (rm -f $@; exit 1)

sh4: sh4inst.vo sh4dec.vo sh4.vo

%.vo: %.v
	$(SHOW) coqc $<
	$(HIDE) coqc -q -I $(DIR)/compcert/lib -R $(DIR)/coq SimSoCCert $<
