# SimSoC-Cert, a Coq library on processor architectures for embedded systems.
# See the COPYRIGHTS and LICENSE files.

NAME := SimSoCCert

MAKEFLAGS := -r -j

.SUFFIXES:

.PHONY: clean clean-all clean-doc default config dist doc install-dist install-doc tags graphdep

COQC := $(COQBIN)coqc

MAKECOQ := $(MAKE) -f Makefile.coq

COMPCERT := Coqlib Integers

FILES := $(COMPCERT) Bitvec Config Exception Functions State Proc \
	Util Semantics SCC Arm Simul

VFILES := $(FILES:%=%.v)

default: Makefile.coq
	$(MAKECOQ) OTHERFLAGS="-dont-load-proofs"

config Makefile.coq:
	coq_makefile -R . $(NAME) $(VFILES) > Makefile.coq

clean:
	rm -f `find . -name \*~ -o -name \*.d -o -name \*.glob -o -name \*.vo` graph.ps graph.dep
	$(MAKECOQ) clean

clean-doc:
	rm -f doc/$(NAME).*.html doc/index.html doc/main.html

tags:
	coqtags $(VFILES)

doc:
	coqdoc --html -toc -g -d doc -R . $(NAME) $(VFILES)
	./createIndex

#ADR := login-linux.inria.fr:liama/www/color

#install-doc:
#	scp doc/coqdoc.css doc/*.html $(ADR)/doc

dist:
	./createDist

install-dist:
	scp $(NAME)_`date +%y%m%d`.tar.gz $(ADR)/$(NAME).tar.gz
	scp CHANGES $(ADR)/CHANGES.$(NAME)

%.vo: %.v
	$(MAKECOQ) OTHERFLAGS="-dont-load-proofs" $@

graphdep: graph.ps

%.ps: %.dep
	cat $< | ../tools/bin/dependot | dot -Tps > $@

graph.dep: $(VFILES)
	cat $(VFILES:%=%.d) | sed -e 's/ .*glob:/:/' -e 's,\./,,g' > $@

%:
	$(MAKECOQ) OTHERFLAGS="-dont-load-proofs" $@
