# SimSoC-Cert, a Coq library on processor architectures for embedded systems.
# See the COPYRIGHTS and LICENSE files.

DIR := ../..

CPPFLAGS := -I$(DIR)/elf # for elf.h and elf_loader.hpp
CXXFLAGS := -Wall -Wextra

default: arm2coq

arm2coq: main.o $(DIR)/elf/elf_loader.o
	$(CXX) $^ $(LDFLAGS) -o $@

main.o: main.cpp $(DIR)/elf/elf_loader.hpp

$(DIR)/elf/elf_loader.hpp $(DIR)/elf/elf_loader.o: FORCE
	$(MAKE) -C $(DIR)/elf $@

clean:
	rm -f arm2coq *.o

FORCE:
