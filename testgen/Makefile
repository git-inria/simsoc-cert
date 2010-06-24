FILES := sum_iterative

.PRECIOUS: $(FILES:%=%.elf) $(FILES:%=%.v)

default: elf2coq $(FILES:%=%.vo)

main.o: main.cpp elf_loader.hpp elf.h

elf_loader.o: elf_loader.cpp elf_loader.hpp elf.h

elf2coq: main.o elf_loader.o
	g++ $^ -o $@

%.elf: %.c
	arm-elf-gcc $< -nostdlib -o $@

%.v: %.elf elf2coq
	./elf2coq $< $@

%.vo: %.v
	coqc -I ../arm6 $<

clean:
	rm -f elf2coq *.elf *.v *.o *.vo
