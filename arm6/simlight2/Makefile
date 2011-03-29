# SimSoC-Cert, a toolkit for generating certified processor simulators
# See the COPYRIGHTS and LICENSE files.

DIR := ..

include $(DIR)/Makefile.common

CPPFLAGS := -I$(DIR)/tools/bin2elf # for elf.h
CFLAGS := -Wall -Wextra -Wno-unused -Werror -g #-fprofile-arcs -ftest-coverage
LDFLAGS :=
LIBRARIES := #-lgcov

SOURCES := slv6_iss.c common.c slv6_condition.c slv6_math.c \
        arm_mmu.c slv6_mode.c slv6_processor.c slv6_status_register.c \
        arm_system_coproc.c elf_loader.c arm_not_implemented.c \
	slv6_iss_printers.c

HEADERS := $(SOURCES:%.c=%.h) slv6_iss_h_prelude.h slv6_iss_c_prelude.h \
        arm_not_implemented.h slv6_iss_expanded.h slv6_iss_grouped.h

EXTRA_SOURCES := slv6_iss_arm_decode_exec.c slv6_iss_arm_decode_store.c \
              slv6_iss_thumb_decode_exec.c slv6_iss_thumb_decode_store.c \
              slv6_iss_expanded.hot.c  slv6_iss_grouped.hot.c \
              slv6_iss_expanded.cold.c slv6_iss_grouped.cold.c

OBJECTS := $(SOURCES:%.c=%.o) $(EXTRA_SOURCES:%.c=%.o) simlight.o

GENFILES_MO := slv6_iss_expanded.hot.c  slv6_iss_grouped.hot.c \
            slv6_iss_expanded.cold.c slv6_iss_grouped.cold.c \
            slv6_iss_expanded.h slv6_iss_grouped.h \
            slv6_iss.h print_sizes.c \
            slv6_iss_arm_decode_exec.c slv6_iss_arm_decode_store.c \
            slv6_iss_thumb_decode_exec.c slv6_iss_thumb_decode_store.c \
            slv6_iss-llvm_generator.hpp slv6_iss_printers.c \
            slv6_iss_printers.h slv6_iss_printers.cpp \
            slv6_iss_printers.hpp

GENFILES := $(GENFILES_MO) slv6_iss.c

.PHONY: default clean

default: simlight2

simlight2: $(OBJECTS)
	$(CC) $(LDFLAGS) $^ -o $@ $(LIBRARIES)

%.o: %.c $(HEADERS)
	$(CC) -c $(CPPFLAGS) $(CFLAGS) $< -o $@

$(GENFILES): $(SIMGEN) ../arm6inst.arm ../arm6syntax.dat ../arm6dec.dat
	$(SIMGEN) -v -oc4dt slv6_iss -ipc ../arm6inst.arm \
		-isyntax ../arm6syntax.dat -idec ../arm6dec.dat \
		-iw weights.1

$(GENFILES_MO): slv6_iss.c

$(SIMGEN): FORCE
	$(MAKE) -C $(DIR)/simgen

../arm6inst.arm ../arm6dec.dat ../arm6syntax.dat: FORCE
	$(MAKE) -C .. $@

clean:
	rm -f $(OBJECTS) $(GENFILES) simlight simlight.opt *.gcda *.gcno
	rm -rf simlight.opt.dSYM

FORCE:
