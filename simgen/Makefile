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
