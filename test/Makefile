C_FILES := sum_iterative sum_recursive sum_direct endian multiply simsoc_new1 \
           test_mem sorting
ARM_FILES := arm_blx2 arm_cflag arm_dpi arm_edsp arm_ldrd_strd arm_ldmstm \
             arm_ldrstr arm_mrs arm_msr arm_multiple arm_swi $(C_FILES) #crypto_short
THUMB_FILES := $(C_FILES)

.PRECIOUS: $(ARM_FILES:%=%_a.elf) $(ARM_FILES:%=%_a.v) $(ARM_FILES:%=%_a.ml) \
     $(THUMB_FILES:%=%_t.elf) $(THUMB_FILES:%=%_t.v) $(THUMB_FILES:%=%_t.ml)

default: $(ARM_FILES:%=%_a.vo) $(ARM_FILES:%=%_a.ml) \
         $(ARM_FILES:%=%_a.cmi) $(ARM_FILES:%=%_a.cmo) \
         $(THUMB_FILES:%=%_t.vo) $(THUMB_FILES:%=%_t.ml) \
         $(THUMB_FILES:%=%_t.cmi) $(THUMB_FILES:%=%_t.cmo)

%.cmi: %.mli ../extract/tmp/extract.cma
	ocamlc -c -I ../extract/tmp extract.cma $<

%.cmo: %.ml %.cmi ../extract/tmp/extract.cma
	ocamlc -c -g -I ../extract/tmp extract.cma $<

%.ml %.mli: %.v %.vo
	./extract_file $<

%.vo: %.v
	coqc -q -R ../coq SimSoCCert $<

%.v: %.elf ../testgen/elf2coq
	../testgen/elf2coq $< $@

%_a.elf: %.c common.h
	arm-elf-gcc $< -nostdlib -lc -lnosys -o $@

%_t.elf: %.c common.h
	arm-elf-gcc -mthumb $< -nostdlib -lc -lnosys -lgcc -o $@

crypto_short_a.elf: crypto_short.c common.h libcrypto/libcrypto.a
	arm-elf-gcc -Ilibcrypto $< -nostdlib libcrypto/libcrypto.a -lc -lgcc -o $@

libcrypto/libcrypto.a: FORCE
	cd libcrypto && $(MAKE)

../testgen/elf2coq: FORCE
	cd ../testgen/ && $(MAKE)

clean:
	rm -f $(ARM_FILES:%=%_a.vo) $(ARM_FILES:%=%_a.v) $(ARM_FILES:%=%_a.elf) \
	      $(ARM_FILES:%=%_a.ml) $(ARM_FILES:%=%_a.mli) \
	      $(ARM_FILES:%=%_a.cmo) $(ARM_FILES:%=%_a.cmi)
	rm -f $(THUMB_FILES:%=%_t.vo) $(THUMB_FILES:%=%_t.v) $(THUMB_FILES:%=%_t.elf) \
	      $(THUMB_FILES:%=%_t.ml) $(THUMB_FILES:%=%_t.mli) \
	      $(THUMB_FILES:%=%_t.cmo) $(THUMB_FILES:%=%_t.cmi)

FORCE:
