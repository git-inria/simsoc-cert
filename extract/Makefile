COMPCERT=../compcert

include $(COMPCERT)/Makefile.config
DIRS=lib common $(ARCH)/$(VARIANT) $(ARCH) backend cfrontend driver

INCLUDES=$(patsubst %,-I $(COMPCERT)/%, $(DIRS))

COQEXEC=coqtop -q $(INCLUDES) -I ../arm6 -R ../coq SimSoCCert -batch -load-vernac-source
#NAME=extract

.PHONY: all extraction tags clean

all: extraction

extraction:
	mkdir -p tmp && \
	$(COQEXEC) ExtractArm6.v

tags:
	otags -sr '.mli' -r .

clean:
	\rm -rf *~
