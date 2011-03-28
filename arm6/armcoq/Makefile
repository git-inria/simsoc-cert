
CPPFLAGS=-I../elf # for elf.h and elf_loader.hpp
CXXFLAGS=-Wall -Wextra

default: arm2coq

arm2coq: main.o ../elf/elf_loader.o
	$(CXX) $^ $(LDFLAGS) -o $@

main.o: main.cpp ../elf/elf_loader.hpp

../elf/elf_loader.hpp ../elf/elf_loader.o: FORCE
	cd ../elf && $(MAKE) $@

clean:
	rm -f arm2coq *.o

FORCE:
