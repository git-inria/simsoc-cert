# SimSoC-Cert, a Coq library on processor architectures for embedded systems.
# See the COPYRIGHTS and LICENSE files.

TARGETS = keepoper indentation oneline_expr keepbincode parsebincode keepsyntax parsesyntax convert_syntax

default: $(TARGETS)

clean:
	rm -f *.cm* *.o *~ $(TARGETS)

lightheadertype.cmx: lightheadertype.ml
	ocamlopt -pp camlp4o -c $< 

lightheadertype.cmo: lightheadertype.ml
	ocamlopt -pp camlp4o librap.cmx $< -o $@

librap.cmx: librap.ml lightheadertype.cmx
	ocamlopt -pp camlp4o -c $< 

librap.cmo: librap.ml lightheadertype.cmo
	ocamlc -pp camlp4o -c $< 

keepoper: keepoper.ml librap.cmx lightheadertype.cmx
	ocamlopt -pp camlp4o librap.cmx $< -o $@

indentation: indentation.ml
	ocamlopt -pp camlp4o $< -o $@

oneline_expr: oneline_expr.ml librap.cmx lightheadertype.cmx
	ocamlopt -pp camlp4o librap.cmx $< -o $@

keepbincode: keepbincode.ml librap.cmx lightheadertype.cmx
	ocamlopt -pp camlp4o librap.cmx $< -o $@

codetype.cmx: codetype.ml librap.cmx lightheadertype.cmx
	ocamlopt -c librap.cmx $< 

codetype.cmo: codetype.ml librap.cmo lightheadertype.cmo
	ocamlc -c librap.cmo $< 

syntaxtype.cmx: syntaxtype.ml librap.cmx lightheadertype.cmx
	ocamlopt -c librap.cmx $< 

syntaxtype.cmo: syntaxtype.ml librap.cmo lightheadertype.cmo
	ocamlc -c librap.cmo $< 

parsebincode: parsebincode.ml librap.cmx codetype.cmx lightheadertype.cmx 
	ocamlopt -pp camlp4o librap.cmx codetype.cmx lightheadertype.cmx parsebincode.ml -o $@

parsesyntax: parsesyntax.ml librap.cmx syntaxtype.cmx lightheadertype.cmx
	ocamlopt -pp camlp4o librap.cmx syntaxtype.cmx lightheadertype.cmx parsesyntax.ml -o $@

keepsyntax: keepsyntax.ml librap.cmx lightheadertype.cmx
	ocamlopt -pp camlp4o librap.cmx lightheadertype.cmx $< -o $@

convert_syntax: convert_syntax.ml 
	ocamlopt -pp camlp4o $< -o $@

testoper:
	./keepoper < arm6inst.txt > resu_keepoper

testbincode:
	./keepbincode < arm6dec.txt > resu_keepbincode

testsyntax:
	./keepsyntax < arm6syntax.txt > resu_keepsyntax
