# SimSoC-Cert, a Coq library on processor architectures for embedded systems.
# See the COPYRIGHTS and LICENSE files.

TARGETS = keepoper indentation oneline_expr keepbincode parsebincode

default: $(TARGETS)

clean:
	rm -f *.cm* *.o *~ $(TARGETS)

keepoper: keepoper.ml
	ocamlopt -pp camlp4o $< -o $@

indentation: indentation.ml
	ocamlopt -pp camlp4o $< -o $@

oneline_expr: oneline_expr.ml
	ocamlopt -pp camlp4o $< -o $@

keepbincode: keepbincode.ml
	ocamlopt -pp camlp4o $< -o $@

codetype.cmx: codetype.ml
	ocamlopt -c $< 

codetype.cmo: codetype.ml
	ocamlc -c $< 

parsebincode: parsebincode.ml codetype.cmx
	ocamlopt -pp camlp4o codetype.cmx parsebincode.ml -o $@
