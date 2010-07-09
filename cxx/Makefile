CPPFLAGS=-I../testgen # for elf.h and elf_loader.hpp
CXXFLAGS=-Wall -Wextra
CC = g++

all: simlight

simlight: simlight.o ../testgen/elf_loader.o arm_iss_base.o

simlight.o: simlight.cpp arm_iss.cpp arm_iss_base.hpp ../testgen/elf_loader.hpp

arm_iss.o: arm_iss.cpp arm_iss_base.hpp

arm_iss.cpp: ../pseudocode/main ../arm6/arm6inst.arm
	../pseudocode/main -ocxx -ipc ../arm6/arm6inst.arm -idec ../arm6/arm6dec.dat >$@.tmp
	mv $@.tmp $@

arm_iss_base.o: arm_iss_base.cpp arm_iss_base.hpp

../pseudocode/main: FORCE
	cd ../pseudocode && $(MAKE)

../arm6/arm6inst.arm: FORCE
	cd ../arm6 && $(MAKE) $@

../testgen/elf_loader.o: FORCE
	cd ../testgen && $(MAKE) $@

diff: arm_iss.cpp arm_iss-ref.cpp
	diff -qw $^

clean:
	rm -f arm_iss.o arm_iss.cpp arm_iss.cpp.tmp

FORCE:
