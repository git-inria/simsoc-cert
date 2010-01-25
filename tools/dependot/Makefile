BIN= ../bin
TARGET= dependot

$(TARGET): $(TARGET).ml
	ocamlc $(TARGET).ml -o $(TARGET)

install: $(TARGET)
	install ${TARGET} $(BIN)

check: $(TARGET) exemple.dot
	cmp exemple.dot exemple-ref.dot


%.dot: %.dep
	cat $< | ./$(TARGET) > $@

%.ps: %.dep
	cat $< | ./$(TARGET) | dot -Tps > $@

clean:
	rm -f *~ *.cm? $(TARGET) exemple.dot exemple.ps

distrib:
	rm -rf build-dependot
	mkdir -p build-dependot
	cp -a Makefile README dependot.ml exemple.dep exemple-ref.dot build-dependot
	tar czf dependot.tar.gz build-dependot
	rm -rf build-dependot

ps: $(TARGET) exemple.ps
