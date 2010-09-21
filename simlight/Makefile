CPPFLAGS=-I../elf # for elf.h
CFLAGS=-Wall -Wextra -Wno-unused -Werror -g
CC = gcc

SOURCES=slv6_iss.c common.c slv6_condition.c slv6_math.c \
 arm_mmu.c slv6_mode.c slv6_processor.c slv6_status_register.c \
 arm_system_coproc.c elf_loader.c arm_not_implemented.c
HEADERS=$(SOURCES:%.c=%.h) slv6_iss_h_prelude.h slv6_iss_c_prelude.h \
 arm_not_implemented.h
OBJECTS=$(SOURCES:%.c=%.o) simlight.o

all: simlight

simlight: $(OBJECTS)
	$(CC) $^ -o $@

%.o: %.c $(HEADERS)
	$(CC) -c $(CPPFLAGS) $(CFLAGS) $< -o $@

slv6_iss.h slv6_iss.c: ../pseudocode/main ../arm6/arm6inst.arm ../arm6/arm6dec.dat
	../pseudocode/main -ocxx slv6_iss -ipc ../arm6/arm6inst.arm \
                           -idec ../arm6/arm6dec.dat
slv6_iss.c: slv6_iss.h

../pseudocode/main: FORCE
	cd ../pseudocode && $(MAKE)

../arm6/arm6inst.arm ../arm6/arm6dec.dat: FORCE
	cd ../arm6 && $(MAKE) $@

clean:
	rm -f $(OBJECTS) slv6_iss.c slv6_iss.h \
              simlight simlight.opt simlight.opt.dSYM *.gcda *.gcno

simlight.opt: FORCE
	gcc simlight.c $(SOURCES:%=--include %) -g -DNDEBUG -O3 \
            -I../elf -o $@

FORCE:
