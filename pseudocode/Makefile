# SimSoC-Cert, a toolkit for generating certified processor simulators
# See the COPYRIGHTS and LICENSE files.

DIR := ..

include $(DIR)/Makefile.common

COMPCERT := $(DIR)/compcert

include $(COMPCERT)/Makefile.config

DIRS := lib common $(ARCH)/$(VARIANT) $(ARCH) backend cfrontend driver

INCLUDES := $(patsubst %,-I $(COMPCERT)/%, $(DIRS))

# command for compilation of Coq files
COQC := coqc -q -noglob -dont-load-proofs $(INCLUDES)

# command for extracting OCaml files from Coq files
COQTOP := coqtop -q $(INCLUDES) -batch -load-vernac-source

.PHONY: default clean tags bintest

default: extraction/Csyntax_print.ml
	$(SHOW) ocamlbuild pseudocode/main
	$(HIDE) cd $(DIR) && \
	$(OCAMLBUILD) \
		pseudocode/main.d.byte \
		pseudocode/main.native \
		pseudocode/main_finalize

extraction/Csyntax_print.ml: extraction extraction.v
	$(SHOW) coqtop extraction.v
	$(HIDE) $(COQTOP) extraction.v && \
	sed -i '2830 s/= Vector.to_list n/v0 = Vector.to_list n v0/' extraction/Csyntax_print.ml # manual eta-expansion with Coq 8.3pl1

extraction:
	mkdir -p extraction

extraction.v: Csyntax_print.vo

clean:
	rm -rf extraction *.vo

tags:
	otags -sr '.mli' -r .

bintest:
	./main -ipc ../arm6/arm6inst.arm -isyntax ../arm6/arm6syntax.dat -idec ../arm6/arm6dec.dat -s 1 -obin-test > test.bin
	./main -ipc ../arm6/arm6inst.arm -isyntax ../arm6/arm6syntax.dat -idec ../arm6/arm6dec.dat -s 1 -oasm-test test
	../elf/bin2elf test.bin test.elf 
	../simlight2/simlight -Adec ../pseudocode/test.elf | perl -p -e "s/[^\t]*\t//" | perl -p -e "s/CPY/MOV/" >tst.asm

.SUFFIXES: .v .vo

.v.vo:
	$(SHOW) coqc $*.v
	$(HIDE) $(COQC) $*.v
