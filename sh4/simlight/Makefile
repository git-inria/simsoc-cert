# SimSoC-Cert, a toolkit for generating certified processor simulators
# See the COPYRIGHTS and LICENSE files.

DIR := ../..

COQ_INCLUDES := -I $(DIR)/coq

include $(DIR)/Makefile.common

default: simlight

######################################################################
# compilation of simlight

CPPFLAGS := #-I$(DIR)/tools/bin2elf
#CFLAGS := -Wall -Wextra -Wno-unused -Werror -g
#CC := ccomp -fstruct-assign -fno-longlong

SOURCES := common.c elf_loader.c sh4_mmu.c slsh4_math.c \
	slsh4_processor.c \
	slsh4_iss.c

OBJECTS := $(SOURCES:%.c=%.o) simlight.o

HEADERS := common.h $(DIR)/tools/bin2elf/elf.h elf_loader.h sh4_mmu.h \
	\
	slsh4_math.h \
	slsh4_processor.h slsh4_status_register.h \
	slsh4_iss_c_prelude.h slsh4_iss_h_prelude.h \
	slsh4_iss.h 

simlight: $(OBJECTS)
	$(CC) $^ -o simlight

%.o: %.c $(HEADERS)
	$(CC) -c $(CPPFLAGS) $(CFLAGS) $< -o $@

slsh4_iss.h slsh4_iss.c: $(SIMGEN) ../sh4.dat
	$(SIMGEN) -ocxx slsh4_iss -sh4 -idat ../sh4.dat

../sh4.dat: FORCE
	$(MAKE) -C .. $(@:../%=%)

simlight.opt: FORCE
	gcc simlight.c $(SOURCES:%=--include %) -g -DNDEBUG -O3 -I../elf -o $@

clean::
	rm -f $(OBJECTS) slsh4_iss.[ch] simlight simlight.opt

######################################################################
# representation of simlight in Coq

.PHONY: proof

proof: libcoq all.vo

all.vo: $(DIR)/coq/Cnotations.vo

.PRECIOUS: all.v

all.c: $(HEADERS) $(SOURCES) simlight.c
	cat $+ | sed -e 's|#include "\(.*\)|//#include "\1|' -e 's|#include <elf.h>|//#include <elf.h>|' > $@

clean::
	rm -f all.c all.v all.glob all.vo

######################################################################
# extraction

ocaml: extraction-libcoq extraction
	$(SHOW) ocamlbuild arm6/simlight/extraction/all.cmo
	$(HIDE) $(OCAMLBUILD) arm6/simlight/extraction/all.cmo

extraction.v: all.vo

######################################################################
# dependency graph

simlight.dep: FORCE
	grep '#include ' $(HEADERS) $(SOURCES) simlight.c | sed -e 's|#include||' -e 's|["<>]||g' -e 's|\([^/]*\)/||g' > $@

clean::
	rm -f simlight.dep

.PHONY: depend

depend: simlight.ps
	gv $< &
