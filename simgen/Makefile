# SimSoC-Cert, a toolkit for generating certified processor simulators
# See the COPYRIGHTS and LICENSE files.

DIR := ..

include $(DIR)/Makefile.common

default: extraction
	sed -i 's/= Vector.to_list n/v0 = Vector.to_list n v0/' extraction/RawCoq_Csyntax.ml # manual eta-expansion
        # REMARK as long as there is only one [Vector.to_list] in the file, it is allowed to not precise the line number (useful in the case this line changes often)
	$(BUILD) simgen/main

extraction.v: RawCoq_Csyntax.vo

clean::
	rm -f RawCoq_Csyntax.vo main


.PHONY: bintest

bintest:
	./main -ipc ../arm6/arm6inst.arm -isyntax ../arm6/arm6syntax.dat -idec ../arm6/arm6dec.dat -s 1 -obin-test > test.bin
	./main -ipc ../arm6/arm6inst.arm -isyntax ../arm6/arm6syntax.dat -idec ../arm6/arm6dec.dat -s 1 -oasm-test test
	../elf/bin2elf test.bin test.elf 
	../simlight2/simlight -Adec ../simgen/test.elf | perl -p -e "s/[^\t]*\t//" | perl -p -e "s/CPY/MOV/" >tst.asm
