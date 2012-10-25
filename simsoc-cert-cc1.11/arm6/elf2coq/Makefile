# SimSoC-Cert, a Coq library on processor architectures for embedded systems.
# See the COPYRIGHTS and LICENSE files.

DIR := ../..

include $(DIR)/Makefile.common

BIN2ELF := $(DIR)/tools/bin2elf

CPPFLAGS := -I$(BIN2ELF) # for elf.h and elf_loader.hpp
CXXFLAGS := -Wall -Wextra

default: elf2coq

elf2coq: main.o $(BIN2ELF)/elf_loader.o
	$(CXX) $^ -o $@

main.o: main.cpp $(BIN2ELF)/elf_loader.hpp

$(BIN2ELF)/elf_loader.o: FORCE
	$(MAKE) -C $(BIN2ELF) $@

clean::
	rm -f elf2coq *.o
