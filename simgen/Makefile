# SimSoC-Cert, a toolkit for generating certified processor simulators
# See the COPYRIGHTS and LICENSE files.

DIR := ..

COQ_INCLUDES := -I $(DIR)/coq

include $(DIR)/Makefile.common

TARGETS := main

default: patch-extraction extraction-libcoq $(TARGETS)

FILES := util ast flatten norm \
	dec gencoqdec genmldec \
	validity gendectest \
	genpc gencoq gencxx \
	codetype lightheadertype syntaxtype \
	ps2cl_ast_trans \
	c2pc CompCert_Driver \
	simlight2 sl2_decoder sl2_patch sl2_print sl2_semantics \
	main

$(TARGETS): $(FILES:%=%.ml) lexer.mll parser.mly RawCoq_Csyntax.v # instead of FORCE to call ocamlbuild only when necessary because ocamlbuild is too slow here
	$(SHOW) ocamlbuild simgen/$@
	$(HIDE) $(OCAMLBUILD) simgen/$@.d.byte simgen/$@.native

.PHONY: patch-extraction

patch-extraction: extraction
	@if test `grep -c 'v0 = Vector.to_list n v0' extraction/RawCoq_Csyntax.ml` -eq 0; then echo sed -i 's/= Vector.to_list n/v0 = Vector.to_list n v0/' extraction/RawCoq_Csyntax.ml; sed -i 's/= Vector.to_list n/v0 = Vector.to_list n v0/' extraction/RawCoq_Csyntax.ml; fi

extraction.v: RawCoq_Csyntax.vo

clean::
	rm -f $(TARGETS) RawCoq_Csyntax.vo

html: RawCoq_Csyntax.v
	mkdir -p html
	$(COQDOC) RawCoq_Csyntax.v

clean::
	rm -rf html
