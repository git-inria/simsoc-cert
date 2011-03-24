C_FILES := sum_iterative sum_recursive sum_direct endian multiply simsoc_new1 \
           test_mem sorting

ARM_FILES := arm_blx2 arm_cflag arm_dpi arm_edsp arm_ldrd_strd arm_ldmstm \
             arm_ldrstr arm_mrs arm_msr arm_multiple arm_swi arm_v6_SADD  \
	     arm_v6_QADD arm_v6_QSUB arm_v6_REV arm_v6 arm_v6_SHADD       \
             arm_v6_SHSUB arm_v6_SML arm_v6_SMM arm_v6_UA arm_v6_UQADD    \
             arm_v6_SMU arm_v6_SSAT arm_v6_SSUB arm_v6_SXTA arm_v6_USUB   \
             arm_v6_SXTB arm_v6_UMAAL arm_v6_UH arm_v6_UQSUB arm_v6_USAD  \
             arm_v6_USAT arm_v6_UXTA arm_v6_UXTB $(C_FILES)

THUMB_FILES := thumb_test thumb_v6 thumb_v6_SXUX thumb_v6_REV thumb_flags $(C_FILES)

###

COQC=coqc -q -noglob -I ../compcert/lib -R ../coq SimSoCCert
COQEXEC=coqtop -q -I ../compcert/lib -R ../coq SimSoCCert

ifeq ($(VERBOSE),1)
  SHOW := @true
  HIDE :=
else
  SHOW := @echo
  HIDE := @
endif

###

default: $(ARM_FILES:%=%_a.vo) $(THUMB_FILES:%=%_t.vo)
	$(SHOW) OCAMLBUILD test/debug
	$(HIDE) cd .. && \
	ocamlbuild -j 2 -no-hygiene -no-links \
		test/debug.byte \
		test/debug_finalize_bc


elf: $(ARM_FILES:%=%_a.elf) $(THUMB_FILES:%=%_t.elf)

.PRECIOUS: $(ARM_FILES:%=%_a.v) $(ARM_FILES:%=%_a.vo) $(ARM_FILES:%=%_a.elf) \
	   $(THUMB_FILES:%=%_t.v) $(THUMB_FILES:%=%_t.vo) $(THUMB_FILES:%=%_t.elf)

%.vo: %.v
	$(SHOW) COQC $<
	$(HIDE) $(COQC) $<
	$(SHOW) COQTOP $<
	$(HIDE) (f=`basename $< .v` ; echo "Cd \"../extract/tmp\". Require Extraction $$f. Extraction Library $$f." | $(COQEXEC)) 2>&1 > /dev/null

%.v: %.elf ../testgen/arm2coq
	$(SHOW) ARM2COQ $< > $@
	$(HIDE) ../testgen/arm2coq $< $@

%_a.elf: %.c common.h
	$(SHOW) ARM-ELF-GCC $< > $@
	$(HIDE) arm-elf-gcc $< -g -nostdlib -lc -lnosys -o $@

%_t.elf: %.c common.h
	$(SHOW) ARM-ELF-GCC $< > $@
	$(HIDE) arm-elf-gcc -mthumb $< -g -nostdlib -lc -lnosys -lgcc -o $@

../testgen/arm2coq: FORCE
	cd ../testgen/ && $(MAKE)

FORCE:

clean:
	rm -f $(ARM_FILES:%=%_a.v) $(ARM_FILES:%=%_a.vo) $(ARM_FILES:%=%_a.elf) \
	      $(THUMB_FILES:%=%_t.v) $(THUMB_FILES:%=%_t.vo) $(THUMB_FILES:%=%_t.elf)