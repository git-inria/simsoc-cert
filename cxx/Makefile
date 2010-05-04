
all: arm_iss.o diff

arm_iss.o: arm_iss.cpp arm_iss_base.hpp

arm_iss.cpp: ../pseudocode/bin/main ../refARMparsing/indentV6.txt
	../pseudocode/bin/main -ocxx -ipc ../refARMparsing/indentV6.txt >$@.tmp
	mv $@.tmp $@

../pseudocode/bin/main: FORCE
	cd ../pseudocode && $(MAKE)

../refARMparsing/indentV6.txt: FORCE
	cd ../refARMparsing && $(MAKE)

diff: arm_iss.cpp arm_iss-ref.cpp
	diff -qw $^

clean:
	rm -f arm_iss.o arm_iss.cpp arm_iss.cpp.tmp

FORCE:
