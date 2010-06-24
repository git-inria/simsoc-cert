FILES := sum_iterative

.PRECIOUS: $(FILES:%=%.elf)

default: elf2coq $(FILES:%=%.v)

main.o: main.cpp elf_loader.hpp elf.h

elf_loader.o: elf_loader.cpp elf_loader.hpp elf.h

elf2coq: main.o elf_loader.o
	g++ $^ -o $@

%.elf: %.c
	arm-elf-gcc $< -nostdlib -o $@

%.v: %.elf elf2coq
	./elf2coq $< $@

clean:
	rm -f *.elf *.v *.o elf2coq
