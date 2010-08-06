CPPFLAGS=-I../elf # for elf.h and elf_loader.hpp
CXXFLAGS=-Wall -Wextra -Wno-unused -g
CC = g++

SOURCES=arm_iss.cpp common.cpp arm_condition.cpp arm_math.cpp \
 arm_math.cpp arm_mmu.cpp arm_mode.cpp arm_processor.cpp arm_status_register.cpp \
 arm_system_coproc.cpp ../elf/elf_loader.cpp
HEADERS=$(SOURCES:%.cpp=%.hpp) arm_iss_h_prelude.hpp arm_iss_c_prelude.hpp \
 arm_not_implemented.hpp
OBJECTS=$(SOURCES:%.cpp=%.o) simlight.o ../elf/elf_loader.o

all: simlight

simlight: $(OBJECTS)
	$(CC) $^ -o $@

%.o: %.cpp $(HEADERS)
	$(CC) -c $(CPPFLAGS) $(CXXFLAGS) $< -o $@

arm_iss.hpp arm_iss.cpp: ../pseudocode/main ../arm6/arm6inst.arm ../arm6/arm6dec.dat
	../pseudocode/main -ocxx arm_iss -ipc ../arm6/arm6inst.arm \
                           -idec ../arm6/arm6dec.dat
arm_iss.cpp: arm_iss.hpp

../pseudocode/main: FORCE
	cd ../pseudocode && $(MAKE)

../arm6/arm6inst.arm ../arm6/arm6dec.dat: FORCE
	cd ../arm6 && $(MAKE) $@

../elf/elf_loader.o: FORCE
	cd ../elf && $(MAKE) $@

clean:
	rm -f $(OBJECTS) arm_iss.cpp arm_iss.hpp \
              simlight simlight.opt *.gcda *.gcno

simlight.opt: FORCE
	g++ simlight.cpp $(SOURCES:%=--include %) -g -DNDEBUG -O3 \
            -I../elf ../elf/elf_loader.o -o $@

FORCE:
