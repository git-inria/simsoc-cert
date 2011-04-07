# SimSoC-Cert, a toolkit for generating certified processor simulators
# See the COPYRIGHTS and LICENSE files.

# WARNING: requires DIR, VFILES and INCLUDES to be defined

include $(DIR)/Makefile.common

.SUFFIXES:

#LIBNAME := SimSoCCert

MAKECOQ := $(MAKE) -f Makefile.coq -r -j OTHERFLAGS='-dont-load-proofs'

#############################################################################
# default target

default: Makefile.coq
	$(MAKECOQ)

#############################################################################
# Makefile.coq: Makefile for compiling Coq files

.PHONY: config

.DELETE_ON_ERROR: Makefile.coq

config Makefile.coq:
	$(SHOW) generate Makefile.coq ...
	$(HIDE) coq_makefile $(INCLUDES) $(VFILES) > Makefile.coq

#############################################################################
# cleaning

clean::
	$(MAKECOQ) clean
	rm -f Makefile.coq

#############################################################################
# coq tags

.PHONY: tags

tags:
	coqtags $(VFILES)

#############################################################################
# html documentation

.PHONY: html

html:
	mkdir -p html
	coqdoc --html -toc -g -d html $(VFILES)
	$(DIR)/tools/coqdoc/createIndex > html/main.html
	cp $(DIR)/tools/coqdoc/coqdoc.css html

#############################################################################
# dependency graph

.PHONY: graphdep

graphdep: graph.ps

%.ps: %.dep build-dependot
	cat $< | $(DEPENDOT) | dot -Tps > $@

graph.dep: $(VFILES)
	cat $(VFILES:%=%.d) | sed -e 's/ .*glob:/:/' -e 's,\.\./,,g' -e 's,\./,,g' -e 's,/,__,g' > $@

clean::
	rm -f graph.ps graph.dep
