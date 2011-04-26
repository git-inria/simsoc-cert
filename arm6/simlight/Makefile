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
#CC := ccomp

SOURCES := common.c elf_loader.c arm_mmu.c arm_system_coproc.c slv6_math.c \
	slv6_mode.c slv6_status_register.c slv6_processor.c slv6_condition.c \
	arm_not_implemented.c slv6_iss.c

OBJECTS := $(SOURCES:%.c=%.o) simlight.o

HEADERS := common.h $(DIR)/tools/bin2elf/elf.h elf_loader.h arm_mmu.h \
	arm_system_coproc.h slv6_math.h \
	slv6_mode.h slv6_status_register.h slv6_processor.h slv6_condition.h \
	arm_not_implemented.h slv6_iss_c_prelude.h slv6_iss_h_prelude.h \
	slv6_iss.h

simlight: $(OBJECTS)
	$(CC) $^ -o simlight

%.o: %.c $(HEADERS)
	$(CC) -c $(CPPFLAGS) $(CFLAGS) $< -o $@

slv6_iss.h slv6_iss.c: $(SIMGEN) ../arm6.pc ../arm6.dec
	$(SIMGEN) -ocxx slv6_iss -ipc ../arm6.pc -idec ../arm6.dec

../arm6.pc ../arm6.dec: FORCE
	$(MAKE) -C .. $(@:../%=%)

simlight.opt: FORCE
	gcc simlight.c $(SOURCES:%=--include %) -g -DNDEBUG -O3 -I../elf -o $@

clean::
	rm -f $(OBJECTS) slv6_iss.[ch] simlight simlight.opt

######################################################################
# representation of simlight in Coq

.PHONY: proof

proof: libcoq all.vo

.PRECIOUS: all.v

%.v: %.c $(SIMGEN)
	$(SIMGEN) -ocompcertc-c $< > $@

clean::
	rm -f all.v all.glob all.vo

######################################################################
# extraction

ocaml: extraction-libcoq extraction
	$(SHOW) ocamlbuild arm6/simlight/extraction/all
	$(HIDE) $(OCAMLBUILD) arm6/simlight/extraction/all.d.byte \
		arm6/simlight/extraction/all.native

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
