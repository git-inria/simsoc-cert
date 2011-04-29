# SimSoC-Cert, a toolkit for generating certified processor simulators
# See the COPYRIGHTS and LICENSE files.

# requires various variables to be defined:
# - see the variables required by Makefile.common
# - VFILES: list of Coq files to be compiled
# provides additional Coq-specific targets to Makefile.common:
#   default, config, coqtags, graphdep

include $(DIR)/Makefile.common

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
	$(SHOW) generate Makefile.coq
	$(HIDE) $(COQ_MAKEFILE) $(VFILES) > Makefile.coq

#############################################################################
# cleaning

clean::
	$(MAKECOQ) clean
	rm -f Makefile.coq

#############################################################################
# coqtags

.PHONY: coqtags

coqtags:
	coqtags $(VFILES)

#############################################################################
# html documentation

html: $(VFILES) $(DIR)/tools/coqdoc/createIndex
	mkdir -p html
	$(COQDOC) $(VFILES)
	$(DIR)/tools/coqdoc/createIndex > html/main.html
	cp $(DIR)/tools/coqdoc/coqdoc.css html

#############################################################################
# dependency graph

.PHONY: graphdep

graphdep: graph.pdf

%.pdf: %.dep build-dependot
	cat $< | $(DEPENDOT) | dot -Tpdf > $@

graph.dep: $(VFILES)
	cat $(VFILES:%=%.d) | sed -e 's/ .*glob:/:/' -e 's,\.\./,,g' -e 's,\./,,g' -e 's,/,__,g' > $@

clean::
	rm -f graph.pdf graph.dep
