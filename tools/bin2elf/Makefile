# SimSoC-Cert, a toolkit for generating certified processor simulators
# See the COPYRIGHTS and LICENSE files.

CXXFLAGS := -Wall -Wextra
CC := g++

.PHONY: default clean

default: bin2elf elf_loader.o

bin2elf: bin2elf.o

bin2elf.o: bin2elf.cpp elf.h

elf_loader.o: elf_loader.cpp elf_loader.hpp elf.h

clean:
	rm -f *.o bin2elf
