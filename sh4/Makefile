# SimSoC-Cert, a Coq library on processor architectures for embedded systems.
# See the COPYRIGHTS and LICENSE files.

.PHONY: default all
all: cbc

GEN := ../pseudocode/main.byt

####

sh4.txt: sh4.txt.gz
	gunzip -c $< > $@

sh4inst.v: c_code.dat $(GEN)
	$(GEN) -sh4 -ipc $< -ocoq-inst > $@ || (rm -f $@; exit 1)

sh4dec.v: c_code.dat $(GEN)
	$(GEN) -sh4 -idec $< -ocoq-dec > $@ || (rm -f $@; exit 1)

patch-inst: sh4.txt sh4inst.txt
	diff -u sh4.txt sh4inst.txt > sh4.patch || exit 0

sh4inst.txt: sh4.txt sh4.patch
	patch sh4.txt sh4.patch -o $@

#

sh4: sh4inst.vo sh4dec.vo sh4.vo

%.vo: %.v
	time -p coqc -q -noglob -R ../coq SimSoCCert $<

#

default: 
	cd .. && \
	ocamlbuild -j 2 -no-hygiene -no-links \
		sh4/instr.d.byte \
		sh4/instr.native \
		sh4/finalize

#

clean:
	rm -f sh4inst.v sh4dec.v sh4.vo

nobackup:
	rm -f *.bak *~ *.dup

cbc: default sh4inst.txt
	cat sh4inst.txt | ./instr > c_code.dat
