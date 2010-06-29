
default: elf2coq

main.o: main.cpp elf_loader.hpp elf.h

elf_loader.o: elf_loader.cpp elf_loader.hpp elf.h

elf2coq: main.o elf_loader.o
	g++ $^ -o $@

clean:
	rm -f elf2coq *.o
