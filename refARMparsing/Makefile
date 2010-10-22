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

oneline_expr: oneline_expr.ml
	ocamlopt -pp camlp4o $< -o $@

keepbincode: keepbincode.ml librap.cmx
	ocamlopt -pp camlp4o  librap.cmx $< -o $@

codetype.cmx: codetype.ml
	ocamlopt -c $< 

codetype.cmo: codetype.ml
	ocamlc -c $< 

parsebincode: parsebincode.ml codetype.cmx
	ocamlopt -pp camlp4o librap.cmx codetype.cmx parsebincode.ml -o $@


keepsyntax: keepsyntax.ml librap.cmx
	ocamlopt -pp camlp4o librap.cmx $< -o $@

testoper:
	./keepoper < arm6inst.txt > resu_keepoper

testbincode:
	./keepbincode < arm6dec.txt > resu_keepbincode
