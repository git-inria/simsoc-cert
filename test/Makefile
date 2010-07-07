FILES := sum_iterative

.PRECIOUS: $(FILES:%=%.elf) $(FILES:%=%.v) $(FILES:%=%.ml)

default: $(FILES:%=%.vo) $(FILES:%=%.ml) $(FILES:%=%.cmi) $(FILES:%=%.cmo)

%.cmi: %.mli ../extract/tmp/extract.cma
	ocamlc -c -I ../extract/tmp extract.cma $<

%.cmo: %.ml ../extract/tmp/extract.cma
	ocamlc -c -g -I ../extract/tmp extract.cma $<

%.ml %.mli: %.v
	./extract_file $<

%.vo: %.v
	coqc -q -R ../coq SimSoCCert $<

%.v: %.elf ../testgen/elf2coq
	../testgen/elf2coq $< $@

%.elf: %.c
	arm-elf-gcc $< -nostdlib -o $@

clean:
	rm -f $(FILES:%=%.vo) $(FILES:%=%.v) $(FILES:%=%.elf) \
		$(FILES:%=%.ml) $(FILES:%=%.mli) \
		$(FILES:%=%.cmo) $(FILES:%=%.cmi)
