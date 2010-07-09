
CPPFLAGS=-I../elf # for elf.h and elf_loader.hpp
CXXFLAGS=-Wall -Wextra
CC = g++

default: elf2coq

elf2coq: main.o ../elf/elf_loader.o

main.o: main.cpp ../elf/elf_loader.hpp

../elf/elf_loader.hpp ../elf/elf_loader.o: FORCE
	cd ../elf && $(MAKE) $@

clean:
	rm -f elf2coq *.o

FORCE:
