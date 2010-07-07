CXXFLAGS=-Wall -Wextra

all: arm_iss.o diff

arm_iss.o: arm_iss.cpp arm_iss_base.hpp

arm_iss.cpp: ../pseudocode/main ../arm6/arm6inst.arm
	../pseudocode/main -ocxx -ipc ../arm6/arm6inst.arm -idec ../arm6/arm6dec.dat >$@.tmp
	mv $@.tmp $@

../pseudocode/main: FORCE
	cd ../pseudocode && $(MAKE)

../arm6/arm6inst.arm: FORCE
	cd ../arm6 && $(MAKE) $@

diff: arm_iss.cpp arm_iss-ref.cpp
	diff -qw $^

clean:
	rm -f arm_iss.o arm_iss.cpp arm_iss.cpp.tmp

FORCE:
