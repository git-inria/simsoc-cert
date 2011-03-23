BIN= ../bin
TARGET= dependot

ifeq ($(VERBOSE),1)
  SHOW := @true
  HIDE :=
else
  SHOW := @echo
  HIDE := @
endif

$(TARGET): $(TARGET).ml
	$(SHOW) OCAMLBUILD $(TARGET)
	$(HIDE) cd ../.. && \
	ocamlbuild -j 2 -no-hygiene -no-links \
		tools/dependot/$(TARGET).native \
		tools/dependot/$(TARGET)_finalize

install: $(TARGET)
	install ${TARGET} $(BIN)

check: $(TARGET) exemple.dot
	cmp exemple.dot exemple-ref.dot


%.dot: %.dep
	cat $< | ./$(TARGET) > $@

%.ps: %.dep
	cat $< | ./$(TARGET) | dot -Tps > $@

clean:
	rm -f *~ $(TARGET) exemple.dot exemple.ps

distrib:
	rm -rf build-dependot
	mkdir -p build-dependot
	cp -a Makefile README dependot.ml exemple.dep exemple-ref.dot build-dependot
	tar czf dependot.tar.gz build-dependot
	rm -rf build-dependot

ps: $(TARGET) exemple.ps
