# SimSoC-Cert, a Coq library on processor architectures for embedded systems.
# See the COPYRIGHTS and LICENSE files.

sh4.txt: Renesas_SH4_2006.pdf
	pdftotext -layout Renesas_SH4_2006.pdf $@

c_code_init.c: instr sh4.txt
	cat sh4.txt | ./instr > $@

instr: 
	ocamlopt -c -w A instr.ml
	ocamlopt str.cmxa -o $@ instr.cmx

clean:
	rm -f *~

c_code.patch:
	diff -u c_code_init.c c_code.c > c_code.patch || exit 0
