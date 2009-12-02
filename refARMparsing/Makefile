targ = keepoper operV6.txt

all : $(targ)

clean :
	rm -f *.cm* *.o *~ $(targ)

keepoper : keepoper.ml
	ocamlopt -pp camlp4o $< -o $@

operV6.txt : keepoper ARMv6.txt
	./keepoper < ARMv6.txt > $@

