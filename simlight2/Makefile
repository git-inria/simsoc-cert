CPPFLAGS=-I../elf # for elf.h
CFLAGS=-Wall -Wextra -Wno-unused -Werror -g
CC = gcc

SOURCES=slv6_iss.c common.c slv6_condition.c slv6_math.c \
 arm_mmu.c slv6_mode.c slv6_processor.c slv6_status_register.c \
 arm_system_coproc.c elf_loader.c arm_not_implemented.c \
 slv6_iss_expanded.c slv6_iss_grouped.c
HEADERS=$(SOURCES:%.c=%.h) slv6_iss_h_prelude.h slv6_iss_c_prelude.h \
 arm_not_implemented.h
OBJECTS=$(SOURCES:%.c=%.o) simlight.o

GENFILES=slv6_iss_expanded.c slv6_iss_grouped.c slv6_iss_expanded.h slv6_iss_grouped.h slv6_iss.h slv6_iss.c

all: simlight

simlight: $(OBJECTS)
	$(CC) $^ -o $@

%.o: %.c $(HEADERS)
	$(CC) -c $(CPPFLAGS) $(CFLAGS) $< -o $@

$(GENFILES): ../pseudocode/main ../arm6/arm6inst.arm ../arm6/arm6dec.dat
	../pseudocode/main -oc4dt slv6_iss -ipc ../arm6/arm6inst.arm \
                           -idec ../arm6/arm6dec.dat
slv6_iss_expanded.c slv6_iss_grouped.h slv6_iss_expanded.c slv6_iss_grouped.h slv6_iss.c: slv6_iss.h

../pseudocode/main: FORCE
	cd ../pseudocode && $(MAKE)

../arm6/arm6inst.arm ../arm6/arm6dec.dat: FORCE
	cd ../arm6 && $(MAKE) $@

clean:
	rm -f $(OBJECTS) $(GEN_FILES) \
              simlight simlight.opt *.gcda *.gcno
	rm -rf  simlight.opt.dSYM

simlight.opt: FORCE
	gcc simlight.c $(SOURCES:%=--include %) -g -DNDEBUG -O3 \
            -I../elf -o $@

FORCE:
