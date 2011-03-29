# SimSoC-Cert, a toolkit for generating certified processor simulators
# See the COPYRIGHTS and LICENSE files.

DIR := ..

include $(DIR)/makefile.common

.PHONY: clean default

CPPFLAGS := -I$(DIR)/tools/bin2elf # for elf.h
CFLAGS := -Wall -Wextra -Wno-unused -Werror -g

SOURCES := slv6_iss.c common.c slv6_condition.c slv6_math.c \
 arm_mmu.c slv6_mode.c slv6_processor.c slv6_status_register.c \
 arm_system_coproc.c elf_loader.c arm_not_implemented.c

HEADERS := $(SOURCES:%.c=%.h) slv6_iss_h_prelude.h slv6_iss_c_prelude.h \
 arm_not_implemented.h

OBJECTS := $(SOURCES:%.c=%.o) simlight.o

default: simlight

simlight: $(OBJECTS)
	$(CC) $^ -o $@

%.o: %.c $(HEADERS)
	$(CC) -c $(CPPFLAGS) $(CFLAGS) $< -o $@

slv6_iss.h slv6_iss.c: $(SIMGEN) ../arm6inst.arm ../arm6dec.dat
	$(SIMGEN) -ocxx slv6_iss -ipc ../arm6inst.arm -idec ../arm6dec.dat

slv6_iss.c: slv6_iss.h

$(SIMGEN): FORCE
	$(MAKE) -C $(DIR)/simgen

../arm6inst.arm ../arm6dec.dat: FORCE
	$(MAKE) -C .. $@

clean:
	rm -f $(OBJECTS) slv6_iss.c slv6_iss.h \
              simlight simlight.opt *.gcda *.gcno
	rm -rf  simlight.opt.dSYM

simlight.opt: FORCE
	gcc simlight.c $(SOURCES:%=--include %) -g -DNDEBUG -O3 -I../elf -o $@

FORCE:
