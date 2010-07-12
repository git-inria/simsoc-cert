CXXFLAGS=-Wall -Wextra
CC = g++

all: bin2elf  elf_loader.o

bin2elf: bin2elf.o

bin2elf.o: bin2elf.cpp elf.h

elf_loader.o: elf_loader.cpp elf_loader.hpp elf.h

clean:
	rm -f *.o
