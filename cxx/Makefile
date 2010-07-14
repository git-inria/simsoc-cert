CPPFLAGS=-I../elf # for elf.h and elf_loader.hpp
CXXFLAGS=-Wall -Wextra -Wno-unused -g
CC = g++

all: simlight

simlight: simlight.o ../elf/elf_loader.o arm_iss_base.o arm_iss.o common.o

simlight.o: simlight.cpp arm_iss.hpp arm_iss_base.hpp ../elf/elf_loader.hpp common.hpp

arm_iss.o: arm_iss.cpp arm_iss.hpp arm_iss_base.hpp common.hpp

common.o: common.cpp common.hpp

arm_iss.hpp arm_iss.cpp: ../pseudocode/main ../arm6/arm6inst.arm ../arm6/arm6dec.dat
	../pseudocode/main -ocxx arm_iss -ipc ../arm6/arm6inst.arm -idec ../arm6/arm6dec.dat
arm_iss.cpp: arm_iss.hpp

arm_iss_base.o: arm_iss_base.cpp arm_iss_base.hpp common.hpp

../pseudocode/main: FORCE
	cd ../pseudocode && $(MAKE)

../arm6/arm6inst.arm ../arm6/arm6dec.dat: FORCE
	cd ../arm6 && $(MAKE) $@

../elf/elf_loader.hpp ../elf/elf_loader.o: FORCE
	cd ../elf && $(MAKE) $@

clean:
	rm -f arm_iss.o arm_iss.cpp arm_iss.hpp arm_iss_base.o simlight.o simlight

FORCE:
