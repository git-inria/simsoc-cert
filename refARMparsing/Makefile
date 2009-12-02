targ = keepoper ARMv6.txt operV6.txt

all : $(targ)

clean :
	rm -f *.cm* *.o *~ $(targ)

keepoper : keepoper.ml
	ocamlopt -pp camlp4o $< -o $@

ARMv6.txt : 
	pdftotext -layout ../ARMv6.pdf && mv ../ARMv6.txt .

operV6.txt : keepoper ARMv6.txt
	./keepoper < ARMv6.txt > $@

