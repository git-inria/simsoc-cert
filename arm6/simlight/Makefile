# SimSoC-Cert, a toolkit for generating certified processor simulators
# See the COPYRIGHTS and LICENSE files.

DIR := ../..

COQ_INCLUDES := -I $(DIR)/coq

include $(DIR)/Makefile.common

CPPFLAGS := -I$(DIR)/tools/bin2elf
CFLAGS := -Wall -Wextra -Wno-unused -Werror -g
#CC := ccomp

SOURCES := slv6_iss.c common.c slv6_condition.c slv6_math.c \
  arm_mmu.c slv6_mode.c slv6_processor.c slv6_status_register.c \
  arm_system_coproc.c elf_loader.c arm_not_implemented.c

HEADERS := $(SOURCES:%.c=%.h) slv6_iss_h_prelude.h slv6_iss_c_prelude.h \
  arm_not_implemented.h

OBJECTS := $(SOURCES:%.c=%.o) simlight.o

default: simlight

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
	rm -f $(OBJECTS) slv6_iss.[ch] simlight simlight.opt *.gcda *.gcno
	rm -rf simlight.opt.dSYM

.PHONY: proof

proof: libcoq slv6_iss.vo simlight.vo

.PRECIOUS: $(SOURCES:%.c=%.v) simlight.v

%.v: %.c $(SIMGEN)
	$(SIMGEN) -ocompcertc-c $< > $@

clean::
	rm -f *.v *.glob *.vo
