# SimSoC-Cert, a Coq library on processor architectures for embedded systems.
# See the COPYRIGHTS and LICENSE files.

all: nc c_code.c

####

sh4.txt: Renesas_SH4_2006.pdf
	pdftotext -layout Renesas_SH4_2006.pdf $@

sh4_mod.txt: sh4.txt sh4.patch
	patch sh4.txt sh4.patch -o $@

nc: instr.ml
	ocamlopt -c -w A instr.ml
	ocamlopt str.cmxa -o instr instr.cmx

dc: instr.ml
	ocamlc -c -g -w A instr.ml
	ocamlc -g str.cma -o instr instr.cmo

bc: instr.ml
	ocamlc -c -w A instr.ml
	ocamlc str.cma -o instr instr.cmo

c_code.c: instr sh4_mod.txt
	cat sh4_mod.txt | ./instr > $@

####

clean:
	rm -f instr instr.top instr.cmi instr.cmo instr.cmx instr.asm instr.s instr.o                instr.cma instr.cmxa instr.a instr.cmi instr.cmo instr.cmi instr.cmx instr.o  instr.annot .cmi .cmo .cmx .o dllinstr_stubs.so
	rm -rf ._bcdi ._ncdi ._d

cleanup:
	rm -f                 instr.cmi instr.cmo instr.cmx instr.asm instr.s instr.o                instr.cma instr.cmxa instr.a instr.cmi instr.cmo instr.cmi instr.cmx instr.o  instr.annot .cmi .cmo .cmx .o dllinstr_stubs.so
	rm -rf ._bcdi ._ncdi ._d

nobackup:
	rm -f *.bak *~ *.dup