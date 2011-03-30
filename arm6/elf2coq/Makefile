# SimSoC-Cert, a Coq library on processor architectures for embedded systems.
# See the COPYRIGHTS and LICENSE files.

DIR := ../..

DIRELF := $(DIR)/tools/bin2elf

CPPFLAGS := -I$(DIRELF) # for elf.h and elf_loader.hpp
CXXFLAGS := -Wall -Wextra

default: arm2coq

arm2coq: main.o $(DIRELF)/elf_loader.o
	$(CXX) $^ $(LDFLAGS) -o $@

main.o: main.cpp $(DIRELF)/elf_loader.hpp

$(DIRELF)/elf_loader.hpp $(DIRELF)/elf_loader.o: FORCE
	$(MAKE) -C $(DIRELF) $@

clean:
	rm -f arm2coq *.o

FORCE:
