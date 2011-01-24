# SimSoC-Cert, a Coq library on processor architectures for embedded systems.
# See the COPYRIGHTS and LICENSE files.

all: cbc

####

sh4.txt: sh4.txt.gz
	gunzip -c $< > $@

patch-inst: sh4.txt sh4_inst.txt
	diff -u sh4.txt sh4_inst.txt > sh4.patch || exit 0

sh4_inst.txt: sh4.txt sh4.patch
	patch sh4.txt sh4.patch -o $@

#

instr.native: c_parse.ml  instr.ml  manual.ml  pdf_page.ml  sh4_section.ml  util.ml
	ocamlbuild -I compcert-1.8/cparser instr.native

instr.d.byte: c_parse.ml  instr.ml  manual.ml  pdf_page.ml  sh4_section.ml  util.ml
	ocamlbuild -I compcert-1.8/cparser instr.d.byte

instr.byte: c_parse.ml  instr.ml  manual.ml  pdf_page.ml  sh4_section.ml  util.ml
	ocamlbuild -I compcert-1.8/cparser instr.byte

#

clean:
	ocamlbuild -clean

nobackup:
	rm -f *.bak *~ *.dup

cbc: instr.byte sh4_inst.txt
	cat sh4_inst.txt | ./instr.byte > c_code.dat
