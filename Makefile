# CoLoR, a Coq library on rewriting and termination.
# See the COPYRIGHTS and LICENSE files.
#
# - Frederic Blanqui, 2005-02-03

NAME := SimSoCCert

MAKEFLAGS := -r -j

.SUFFIXES:

.PHONY: clean clean-all clean-doc default config dist doc install-dist install-doc tags

COQC := $(COQBIN)coqc

MAKECOQ := $(MAKE) -f Makefile.coq

VFILES := $(shell find . -name \*.v)

default: Makefile.coq
	$(MAKECOQ) OTHERFLAGS="-dont-load-proofs"

config Makefile.coq:
	coq_makefile -R . $(NAME) $(VFILES) > Makefile.coq
	$(MAKECOQ) depend

clean:
	rm -f `find . -name \*~`
	$(MAKECOQ) clean

clean-doc:
	rm -f doc/$(NAME).*.html doc/index.html

tags:
	coqtags $(VFILES)

doc:
	coqdoc --html -g -d doc -R . $(NAME) $(VFILES)
	./createIndex

ADR := login-linux.inria.fr:liama/www/color

install-doc:
	scp doc/coqdoc.css doc/*.html $(ADR)/doc

dist:
	./createDist

install-dist:
	scp $(NAME)_`date +%y%m%d`.tar.gz $(ADR)/$(NAME).tar.gz
	scp CHANGES $(ADR)/CHANGES.$(NAME)

%.vo: %.v
	$(MAKECOQ) OTHERFLAGS="-dont-load-proofs" $@

%:
	$(MAKECOQ) OTHERFLAGS="-dont-load-proofs" $@
