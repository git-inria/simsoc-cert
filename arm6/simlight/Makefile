# SimSoC-Cert, a toolkit for generating certified processor simulators
# See the COPYRIGHTS and LICENSE files.

DIR := ..

SIMGEN := $(DIR)/simgen/main

.PHONY: clean default

CPPFLAGS := -I../elf # for elf.h
CFLAGS := -Wall -Wextra -Wno-unused -Werror -g
CC := gcc

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

slv6_iss.h slv6_iss.c: $(SIMGEN) $(DIR)/arm6/arm6inst.arm $(DIR)/arm6/arm6dec.dat
	$(SIMGEN) -ocxx slv6_iss -ipc $(DIR)/arm6/arm6inst.arm \
                           -idec $(DIR)/arm6/arm6dec.dat

slv6_iss.c: slv6_iss.h

$(SIMGEN): FORCE
	$(MAKE) -C $(DIR)/simgen

$(DIR)/arm6/arm6inst.arm $(DIR)/arm6/arm6dec.dat: FORCE
	$(MAKE) -C $(DIR)/arm6 $@

clean:
	rm -f $(OBJECTS) slv6_iss.c slv6_iss.h \
              simlight simlight.opt *.gcda *.gcno
	rm -rf  simlight.opt.dSYM

simlight.opt: FORCE
	gcc simlight.c $(SOURCES:%=--include %) -g -DNDEBUG -O3 -I../elf -o $@

FORCE:
