# SimSoC-Cert, a toolkit for generating certified processor simulators
# See the COPYRIGHTS and LICENSE files.

DIR := ..

include $(DIR)/compcert/Makefile.config
include $(DIR)/Makefile.common

DIRS := lib common $(ARCH)/$(VARIANT) $(ARCH) backend cfrontend driver

INCLUDES := $(patsubst %,-I $(DIR)/compcert/%, $(DIRS))

# command for compilation of Coq files
COQC := coqc -q -noglob -dont-load-proofs $(INCLUDES)

# command for extracting OCaml files from Coq files
COQTOP := coqtop -q $(INCLUDES) -batch -load-vernac-source

.PHONY: default clean tags bintest

default: main

main: extraction/RawCoq_Csyntax.ml
	$(BUILD) simgen/main

extraction/RawCoq_Csyntax.ml: extraction extraction.v
	$(SHOW) coqtop extraction.v
	$(HIDE) $(COQTOP) extraction.v && \
	sed -i 's/= Vector.to_list n/v0 = Vector.to_list n v0/' extraction/RawCoq_Csyntax.ml # manual eta-expansion with Coq 8.3pl1
        # REMARK as long as there is only one [Vector.to_list] in the file, it is allowed to not precise the line number (useful in the case this line changes often)

extraction:
	mkdir -p extraction

extraction.v: RawCoq_Csyntax.vo

clean:
	rm -rf extraction *.vo

tags:
	otags -sr '.mli' -r .

bintest:
	./main -ipc ../arm6/arm6inst.arm -isyntax ../arm6/arm6syntax.dat -idec ../arm6/arm6dec.dat -s 1 -obin-test > test.bin
	./main -ipc ../arm6/arm6inst.arm -isyntax ../arm6/arm6syntax.dat -idec ../arm6/arm6dec.dat -s 1 -oasm-test test
	../elf/bin2elf test.bin test.elf 
	../simlight2/simlight -Adec ../simgen/test.elf | perl -p -e "s/[^\t]*\t//" | perl -p -e "s/CPY/MOV/" >tst.asm

.SUFFIXES: .v .vo

.v.vo:
	$(SHOW) coqc $<
	$(HIDE) $(COQC) $<
