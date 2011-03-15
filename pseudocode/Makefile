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
	$(COQEXEC) ExtractPseudocode.v
        # FIXME determine if it is necessary to : rm -f tmp/*.ml tmp/*.mli
        #       after the 'mkdir'

default: 
#	ocamlbuild -j 2 -no-hygiene -no-links -ocamlopt 'ocamlopt -unsafe -noassert -inline 10000' 
	cd .. && \
	ocamlbuild -j 2 -no-hygiene -no-links -ocamlopt 'ocamlopt -unsafe -noassert ' \
		pseudocode/main.d.byte \
		pseudocode/main.native \
		pseudocode/finalize
        # FIXME determine how to choose dynamically ocamlopt.opt or ocamlopt in ocamlbuild
        # FIXME activate inlining at least just for pseudocode part, as was previously actived


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
