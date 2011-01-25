# SimSoC-Cert, a Coq library on processor architectures for embedded systems.
# See the COPYRIGHTS and LICENSE files.

.SUFFIXES:

.PHONY: default clean depend tags clean-all dist install-dist

ifeq ($(VERBOSE),1)
  SHOW := @true
  HIDE :=
else
  SHOW := @echo
  HIDE := @
endif

LIBS := str
CMAFILES := $(LIBS:%=%.cma)
CMXAFILES := $(LIBS:%=%.cmxa)

ARMDIR := ../refARMparsing

INCLUDES := -I $(ARMDIR)

FRAGILE := -w Ae -warn-error Ae

WARNINGS = -w A -warn-error A

OCAMLC = ocamlc -g $(INCLUDES) $(WARNINGS)
OCAMLLEX := ocamllex
OCAMLYACC := ocamlyacc -v
OCAMLDEP := ocamldep $(INCLUDES)
OCAMLOPT = ocamlopt -unsafe -noassert -inline 10000 $(INCLUDES) $(WARNINGS)

# the order is important !
PARSERS := parser lexer
FILES := Cabs util ast dec validity $(PARSERS) c2pc genpc norm flatten gencxx gencoq gencoqdec gencoqdecsh4 genmldec gendectest sl2_patch sl2_semantics sl2_decoder sl2_print simlight2


CMOFILES = $(FILES:%=%.cmo)
CMXFILES = $(FILES:%=%.cmx)

BINFILES := main

BINS := $(BINFILES:%=%)
BYTS := $(BINS:%=%.byt)
OPTS := $(BINS:%=%.opt)

.PRECIOUS: $(BINFILES:%=%.cmo) $(BINFILES:%=%.cmx) $(PARSERS:%=%.ml)

default: $(CMOFILES) $(CMXFILES) $(BYTS) $(OPTS) $(BINS)

%: %.opt
	ln -f -s $*.opt $*

%: %.byt
	ln -f -s $*.byt $*

%.byt: %.cmo
	$(SHOW) OCAMLC -o $@
	$(HIDE) $(OCAMLC) -o $@ $(CMAFILES) $(CMOFILES) $<

%.opt: %.cmx
	$(SHOW) OCAMLOPT -o $@
	$(HIDE) $(OCAMLOPT) -o $@ $(CMXAFILES) $(CMXFILES) $<
	$(SHOW) STRIP $@
	$(HIDE) strip $@

# files with fragile pattern-matching allowed

FRAGILE_FILES := ast flatten genpc norm gencxx c2pc sl2_patch sl2_semantics sl2_decoder sl2_print simlight2 gencoq gendectest

$(FRAGILE_FILES:%=%.cmo) $(FRAGILE_FILES:%=%.cmx): WARNINGS = $(FRAGILE)

# default compilation rules

%.ml %.mli: %.mly
	$(SHOW) OCAMLYACC $*.mly
	$(HIDE) $(OCAMLYACC) $*.mly

%.ml: %.mll
	$(SHOW) OCAMLLEX $*.mll
	$(HIDE) $(OCAMLLEX) $*.mll

%.cmi: %.mli
	$(SHOW) OCAMLC -c $*.mli
	$(HIDE) $(OCAMLC) -c $*.mli

%.cmo: %.ml
	$(SHOW) OCAMLC -c $*.ml
	$(HIDE) $(OCAMLC) -c $*.ml

%.cmx: %.ml
	$(SHOW) OCAMLOPT -c $*.ml
	$(HIDE) $(OCAMLOPT) -c $*.ml

# other targets

tags:
	otags -sr '.mli' -r .

clean:
	rm -f *~ *.cm* *.o $(PARSERS:%=%.ml) $(PARSERS:%=%.output)

#.depend:
#	touch .depend

.depend depend: $(PARSERS:%=%.ml)
	$(SHOW) OCAMLDEP
	$(HIDE) $(OCAMLDEP) $(FILES:%=%.ml) $(BINFILES:%=%.ml) > .depend

parser.cmi: ast.cmi

bintest:
	./main -ipc ../arm6/arm6inst.arm -isyntax ../arm6/arm6syntax.dat -idec ../arm6/arm6dec.dat -s 1 -obin-test > test.bin
	./main -ipc ../arm6/arm6inst.arm -isyntax ../arm6/arm6syntax.dat -idec ../arm6/arm6dec.dat -s 1 -oasm-test test
	../elf/bin2elf test.bin test.elf 
	../simlight2/simlight -Adec ../pseudocode/test.elf | perl -p -e "s/[^\t]*\t//" | perl -p -e "s/CPY/MOV/" >tst.asm

sh4inst: default
	ocamlrun -b ./main.byt -sh4 -ipc  ../sh4/c_code.dat -ocoq-inst > sh4inst.v && coqide -R ../coq SimSoCCert sh4inst.v

sh4dec: default
	coqc -R ../coq SimSoCCert sh4inst.v
	ocamlrun -b ./main.byt -sh4 -idec ../sh4/c_code.dat -ocoq-dec  > sh4dec.v  && coqide -R ../coq SimSoCCert sh4dec.v

include .depend
