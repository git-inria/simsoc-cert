# SimSoC-Cert, a toolkit for generating certified processor simulators
# See the COPYRIGHTS and LICENSE files.

C_FILES := sum_recursive sum_direct endian multiply simsoc_new1 \
	test_mem sorting

SH_FILES := $(C_FILES)

#THUMB_FILES := $(C_FILES)

default: $(SH_FILES:%=%_a.elf) $(THUMB_FILES:%=%_t.elf)

######################################################################
# generation of elf files

%_a.elf: %.c common.h
	sh-elf-gcc -ml $< -g -nostdlib -lc -lnosys -o $@

%_t.elf: %.c common.h
	sh-elf-gcc -ml -mthumb $< -g -nostdlib -lc -lnosys -lgcc -o $@

clean::
	rm -f $(SH_FILES:%=%_a.elf) $(THUMB_FILES:%=%_t.elf)

######################################################################
# checking Coq simulator

DIR := ../..

COQ_INCLUDES := -I $(DIR)/coq -I $(DIR)/sh4/coq

include $(DIR)/Makefile.common

.PHONY: check-coq

check-coq: default extraction
	$(SHOW) ocamlbuild sh4/test/main
	$(HIDE) $(OCAMLBUILD) sh4/test/main.d.byte # assembler error with native compilation

extraction.v: $(SH_FILES:%=%_a.vo) $(THUMB_FILES:%=%_t.vo)
	$(SHOW) generate $@
	$(HIDE) (echo 'Cd "extraction".'; for i in $(SH_FILES:%=%_a) $(THUMB_FILES:%=%_t); do echo "Require Extraction $$i. Extraction Library $$i."; done) > $@

%.v: %.elf ../elf2coq/elf2coq
	../elf2coq/elf2coq $< $@

../elf2coq/elf2coq: FORCE
	$(MAKE) -C ../elf2coq

clean::
	rm -f extraction.v \
		$(SH_FILES:%=%_a.v) $(THUMB_FILES:%=%_t.v) \
		$(SH_FILES:%=%_a.vo) $(THUMB_FILES:%=%_t.vo)
