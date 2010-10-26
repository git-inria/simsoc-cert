# SimSoC-Cert, a Coq library on processor architectures for embedded systems.
# See the COPYRIGHTS and LICENSE files.

TARGETS = keepoper indentation oneline_expr keepbincode parsebincode keepsyntax

default: $(TARGETS)

clean:
	rm -f *.cm* *.o *~ $(TARGETS)


librap.cmx: librap.ml
	ocamlopt -pp camlp4o -c $< 

librap.cmo: librap.ml
	ocamlc -pp camlp4o -c $< 

keepoper: keepoper.ml librap.cmx
	ocamlopt -pp camlp4o librap.cmx $< -o $@

indentation: indentation.ml
	ocamlopt -pp camlp4o $< -o $@

oneline_expr: oneline_expr.ml librap.cmx
	ocamlopt -pp camlp4o librap.cmx $< -o $@

keepbincode: keepbincode.ml librap.cmx
	ocamlopt -pp camlp4o librap.cmx $< -o $@

codetype.cmx: codetype.ml librap.cmx
	ocamlopt -c librap.cmx $< 

codetype.cmo: codetype.ml librap.cmo
	ocamlc -c librap.cmo $< 

syntaxtype.cmx: syntaxtype.ml librap.cmx
	ocamlopt -c librap.cmx $< 

syntaxtype.cmo: syntaxtype.ml librap.cmo
	ocamlc -c librap.cmo $< 

parsebincode: parsebincode.ml librap.cmx codetype.cmx 
	ocamlopt -pp camlp4o librap.cmx codetype.cmx parsebincode.ml -o $@

parsesyntax: parsesyntax.ml librap.cmx syntaxtype.cmx 
	ocamlopt -pp camlp4o librap.cmx syntaxtype.cmx parsesyntax.ml -o $@


keepsyntax: keepsyntax.ml librap.cmx
	ocamlopt -pp camlp4o librap.cmx $< -o $@

testoper:
	./keepoper < arm6inst.txt > resu_keepoper

testbincode:
	./keepbincode < arm6dec.txt > resu_keepbincode
