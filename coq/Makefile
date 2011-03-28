# SimSoC-Cert, a toolkit for generating certified processor simulators
# See the COPYRIGHTS and LICENSE files.

DIR := ..

NAME := SimSoCCert

MAKEFLAGS := -r -j

.SUFFIXES:

.PHONY: clean clean-all clean-doc default config dist doc install-dist \
	install-doc tags graphdep dependot

COQC := $(COQBIN)coqc

MAKECOQ := $(MAKE) -f Makefile.coq

FILES := Message Bitvec Util Semantics \
	Arm_Config Arm_Exception Arm_Functions Arm_State Arm_Proc Arm_SCC Arm \
	Sh4_Config               Sh4_Functions Sh4_State Sh4_Proc         Sh4 \
	Simul Extraction

VFILES := $(FILES:%=%.v)

default: Makefile.coq
	$(MAKECOQ) OTHERFLAGS="-dont-load-proofs"

config Makefile.coq:
	coq_makefile -I ../compcert/lib -R . $(NAME) $(VFILES) > Makefile.coq

clean: clean-doc
	rm -f graph.ps graph.dep
	$(MAKECOQ) clean

clean-doc:
	rm -f doc/$(NAME).*.html doc/index.html doc/main.html

tags:
	coqtags $(VFILES)

doc:
	coqdoc --html -toc -g -d doc -R . $(NAME) $(VFILES)
	./createIndex

#############################################################################
# dependency graph

graphdep: graph.ps

%.ps: %.dep dependot
	cat $< | $(DIR)/tools/dependot/dependot | dot -Tps > $@

dependot:
	$(MAKE) -C $(DIR)/tools/dependot

graph.dep: $(VFILES)
	cat $(VFILES:%=%.d) | sed -e 's/ .*glob:/:/' -e 's,\.\./,,g' -e 's,\./,,g' -e 's,/,__,g' > $@

#############################################################################

#%.vo: %.v
#	$(MAKECOQ) OTHERFLAGS="-dont-load-proofs" $@

%:
	$(MAKECOQ) OTHERFLAGS="-dont-load-proofs" $@
