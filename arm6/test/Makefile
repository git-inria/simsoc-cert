# SimSoC-Cert, a toolkit for generating certified processor simulators
# See the COPYRIGHTS and LICENSE files.

C_FILES := sum_iterative sum_recursive sum_direct endian multiply simsoc_new1 \
           test_mem sorting

ARM_FILES := arm_blx2 arm_cflag arm_dpi arm_edsp arm_ldrd_strd arm_ldmstm \
             arm_ldrstr arm_mrs arm_msr arm_multiple arm_swi arm_v6_SADD  \
	     arm_v6_QADD arm_v6_QSUB arm_v6_REV arm_v6 arm_v6_SHADD       \
             arm_v6_SHSUB arm_v6_SML arm_v6_SMM arm_v6_UA arm_v6_UQADD    \
             arm_v6_SMU arm_v6_SSAT arm_v6_SSUB arm_v6_SXTA arm_v6_USUB   \
             arm_v6_SXTB arm_v6_UMAAL arm_v6_UH arm_v6_UQSUB arm_v6_USAD  \
             arm_v6_USAT arm_v6_UXTA arm_v6_UXTB $(C_FILES)

THUMB_FILES := thumb_test thumb_v6 thumb_v6_SXUX thumb_v6_REV thumb_flags \
	$(C_FILES)

default: $(ARM_FILES:%=%_a.elf) $(THUMB_FILES:%=%_t.elf)

######################################################################
# generation of elf files

%_a.elf: %.c common.h
	arm-elf-gcc $< -g -nostdlib -lc -lnosys -o $@

%_t.elf: %.c common.h
	arm-elf-gcc -mthumb $< -g -nostdlib -lc -lnosys -lgcc -o $@

clean::
	rm -f $(ARM_FILES:%=%_a.elf) $(THUMB_FILES:%=%_t.elf)

######################################################################
# checking Coq simulator

DIR := ../..

COQ_INCLUDES := -I $(DIR)/coq -I $(DIR)/arm6/coq

include $(DIR)/Makefile.common

.PHONY: check-coq

check-coq: default extraction
	$(SHOW) ocamlbuild arm6/test/debug
	$(HIDE) $(OCAMLBUILD) arm6/test/debug.native

extraction.v: $(ARM_FILES:%=%_a.vo) $(THUMB_FILES:%=%_t.vo)
	$(SHOW) generate $@
	$(HIDE) (for i in $(ARM_FILES:%=%_a) $(THUMB_FILES:%=%_t); do echo "Require Extraction $$i. Extraction Library $$i."; done) > $@

%.v: %.elf ../elf2coq/elf2coq
	../elf2coq/elf2coq $< $@

../elf2coq/elf2coq: FORCE
	$(MAKE) -C ../elf2coq

clean::
	rm -f extraction.v \
		$(ARM_FILES:%=%_a.v) $(THUMB_FILES:%=%_t.v) \
		$(ARM_FILES:%=%_a.vo) $(THUMB_FILES:%=%_t.vo)
