CPPFLAGS=-I../elf # for elf.h
CFLAGS=-Wall -Wextra -Wno-unused -g
CC = gcc

SOURCES=arm_iss.c common.c arm_condition.c arm_math.c \
 arm_math.c arm_mmu.c arm_mode.c arm_processor.c arm_status_register.c \
 arm_system_coproc.c elf_loader.c
HEADERS=$(SOURCES:%.c=%.h) arm_iss_h_prelude.h arm_iss_c_prelude.h \
 arm_not_implemented.h
OBJECTS=$(SOURCES:%.c=%.o) simlight.o ../elf/elf_loader.o

all: simlight

simlight: $(OBJECTS)
	$(CC) $^ -o $@

%.o: %.c $(HEADERS)
	$(CC) -c $(CPPFLAGS) $(CFLAGS) $< -o $@

arm_iss.h arm_iss.c: ../pseudocode/main ../arm6/arm6inst.arm ../arm6/arm6dec.dat
	../pseudocode/main -ocxx arm_iss -ipc ../arm6/arm6inst.arm \
                           -idec ../arm6/arm6dec.dat
arm_iss.c: arm_iss.h

../pseudocode/main: FORCE
	cd ../pseudocode && $(MAKE)

../arm6/arm6inst.arm ../arm6/arm6dec.dat: FORCE
	cd ../arm6 && $(MAKE) $@

clean:
	rm -f $(OBJECTS) arm_iss.c arm_iss.h \
              simlight simlight.opt *.gcda *.gcno

simlight.opt: FORCE
	g++ simlight.c $(SOURCES:%=--include %) -g -DNDEBUG -O3 \
            -I../elf ../elf/elf_loader.o -o $@

FORCE:
