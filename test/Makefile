FILES := sum_iterative sum_recursive sum_direct arm_blx2 arm_cflag arm_dpi \
 arm_edsp arm_ldrd_strd arm_ldmstm arm_ldrstr arm_mrs arm_msr arm_multiple \
 arm_swi endian multiply simsoc_new1 test_mem sorting # crypto_short

.PRECIOUS: $(FILES:%=%.elf) $(FILES:%=%.v) $(FILES:%=%.ml)

default: $(FILES:%=%.vo) $(FILES:%=%.ml) $(FILES:%=%.cmi) $(FILES:%=%.cmo)

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

%.elf: %.c common.h
	arm-elf-gcc $< -nostdlib -lc -lnosys -o $@

crypto_short.elf: crypto_short.c common.h libcrypto/libcrypto.a
	arm-elf-gcc -Ilibcrypto $< -nostdlib libcrypto/libcrypto.a -lc -lgcc -o $@

libcrypto/libcrypto.a: FORCE
	cd libcrypto && $(MAKE)

../testgen/elf2coq: FORCE
	cd ../testgen/ && $(MAKE)

clean:
	rm -f $(FILES:%=%.vo) $(FILES:%=%.v) $(FILES:%=%.elf) \
		$(FILES:%=%.ml) $(FILES:%=%.mli) \
		$(FILES:%=%.cmo) $(FILES:%=%.cmi)

FORCE:
