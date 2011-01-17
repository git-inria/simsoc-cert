# SimSoC-Cert, a Coq library on processor architectures for embedded systems.
# See the COPYRIGHTS and LICENSE files.

all: extract_compcert nc

####

extract_compcert: compcert-1.8.tgz
	tar xzvf $< 

nc: export_c_ast.ml
	ocamlbuild -I compcert-1.8/cparser export_c_ast.native

output_value: ../sh4/c_code.c export_c_ast.native
	cat ../sh4/c_code.c | ./export_c_ast.native > c_code.dat

####

clean:
	ocamlbuild -clean

clean_compcert:
	rm -rf compcert-1.8

clean_dat:
	rm c_code.dat

nobackup:
	rm -f *.bak *~ *.dup