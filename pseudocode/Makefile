# SimSoC-Cert, a Coq library on processor architectures for embedded systems.
# See the COPYRIGHTS and LICENSE files.

COMPCERT=../compcert

include $(COMPCERT)/Makefile.config
DIRS=lib common $(ARCH)/$(VARIANT) $(ARCH) backend cfrontend driver

INCLUDES=$(patsubst %,-I $(COMPCERT)/%, $(DIRS))

COQC=coqc -q -noglob $(INCLUDES)
COQEXEC=coqtop -q $(INCLUDES) -I ../pseudocode -batch -load-vernac-source

FILES=Csyntax_print.v

.PHONY: all proof extraction default nobackup tags bintest

all: proof extraction default

proof: $(FILES:.v=.vo)

extraction:
	cd ../extract && \
	mkdir -p tmp && \
	$(COQEXEC) ExtractPseudocode.v && \
	sed -i '2830 s/= Vector.to_list n/v0 = Vector.to_list n v0/' tmp/Csyntax_print.ml # manual eta-expansion with "Coq 8.3pl1 (January 2011)"
        # FIXME determine if it is necessary to : rm -f tmp/*.ml tmp/*.mli
        #       after or before the 'mkdir'

default:
	cd .. && \
	ocamlbuild -j 2 -no-hygiene -no-links \
		pseudocode/main.d.byte \
		pseudocode/main.native \
		pseudocode/main_finalize

nobackup:
	rm -f *.bak *~ *.dup

tags:
	otags -sr '.mli' -r .

bintest:
	./main -ipc ../arm6/arm6inst.arm -isyntax ../arm6/arm6syntax.dat -idec ../arm6/arm6dec.dat -s 1 -obin-test > test.bin
	./main -ipc ../arm6/arm6inst.arm -isyntax ../arm6/arm6syntax.dat -idec ../arm6/arm6dec.dat -s 1 -oasm-test test
	../elf/bin2elf test.bin test.elf 
	../simlight2/simlight -Adec ../pseudocode/test.elf | perl -p -e "s/[^\t]*\t//" | perl -p -e "s/CPY/MOV/" >tst.asm

.SUFFIXES: .v .vo

.v.vo:
	@echo "COQC $*.v"
	@$(COQC) $*.v
