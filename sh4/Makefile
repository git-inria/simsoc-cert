# SimSoC-Cert, a Coq library on processor architectures for embedded systems.
# See the COPYRIGHTS and LICENSE files.

.PHONY: default all
all: cbc sh4

GEN := ../pseudocode/main

ifeq ($(VERBOSE),1)
  SHOW := @true
  HIDE :=
else
  SHOW := @echo
  HIDE := @
endif

####

sh4.txt: sh4.txt.gz
	$(SHOW) GUNZIP $< $@
	$(HIDE) gunzip -c $< > $@

sh4inst.v: sh4.dat $(GEN)
	$(SHOW) PSEUDOCODE $< $@
	$(HIDE) $(GEN) -sh4 -ipc $< -ocoq-inst > $@ || (rm -f $@; exit 1)

sh4dec.v: sh4.dat $(GEN)
	$(SHOW) PSEUDOCODE $< $@
	$(HIDE) $(GEN) -sh4 -idec $< -ocoq-dec > $@ || (rm -f $@; exit 1)

patch-inst: sh4.txt sh4inst.txt
	diff -u sh4.txt sh4inst.txt > sh4.patch || exit 0

sh4inst.txt: sh4.txt sh4.patch
	$(SHOW) PATCH sh4.patch $@
	$(HIDE) patch sh4.txt sh4.patch -o $@

#

sh4: sh4inst.vo sh4dec.vo sh4.vo

%.vo: %.v
	$(SHOW) COQC $<
	$(HIDE) time -p coqc -q -noglob -I ../compcert/lib -R ../coq SimSoCCert $<

#

default: 
	$(SHOW) OCAMLBUILD sh4/instr
	$(HIDE) cd .. && \
	ocamlbuild -j 2 -no-hygiene -no-links \
		sh4/instr.d.byte \
		sh4/instr.native \
		sh4/instr_finalize

#

clean:
	rm -f sh4inst.v sh4dec.v sh4inst.vo sh4dec.vo sh4.vo

nobackup:
	rm -f *.bak *~ *.dup

cbc: default sh4inst.txt
	$(SHOW) SH4 sh4inst.txt > sh4.dat
	$(HIDE) cat sh4inst.txt | ./instr > sh4.dat
