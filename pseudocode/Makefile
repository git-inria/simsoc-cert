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

INCLUDES :=

FRAGILE := -w Ae -warn-error Ae

WARNINGS = -w A -warn-error A

OCAMLC = ocamlc -g $(INCLUDES) $(WARNINGS)
OCAMLLEX := ocamllex
OCAMLYACC := ocamlyacc -v
OCAMLDEP := ocamldep $(INCLUDES)
OCAMLOPT = ocamlopt -unsafe -noassert -inline 10000 $(INCLUDES) $(WARNINGS)

# the order is important !
PARSERS := parser lexer
FILES := util ast $(PARSERS) genpc preproc gencxx gencoq

CMOFILES = $(FILES:%=%.cmo)
CMXFILES = $(FILES:%=%.cmx)

BIN_FILES := main

BINS := $(BIN_FILES:%=bin/%)
BYTS := $(BINS:%=%.byt)
OPTS := $(BINS:%=%.opt)

.PRECIOUS: $(BIN_FILES:%=%.cmo) $(BIN_FILES:%=%.cmx) $(PARSERS:%=%.ml)

default: bin $(CMOFILES) $(CMXFILES) $(BYTS) $(OPTS) $(BINS)

bin:
	mkdir -p bin

bin/%: bin/%.opt
	cd bin; ln -f -s $*.opt $*

bin/%: bin/%.byt
	cd bin; ln -f -s $*.byt $*

bin/%.byt: %.cmo
	$(SHOW) OCAMLC -o $@
	$(HIDE) $(OCAMLC) -o $@ $(CMAFILES) $(CMOFILES) $<

bin/%.opt: %.cmx
	$(SHOW) OCAMLOPT -o $@
	$(HIDE) $(OCAMLOPT) -o $@ $(CMXAFILES) $(CMXFILES) $<
	$(SHOW) STRIP $@
	$(HIDE) strip $@

# files with fragile pattern-matching allowed

FRAGILE_FILES := ast genpc preproc gencxx gencoq

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
	$(HIDE) $(OCAMLDEP) $(FILES:%=%.ml) $(BIN_FILES:%=%.ml) > .depend

parser.cmi: ast.cmi

include .depend
