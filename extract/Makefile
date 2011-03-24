COMPCERT=../compcert

include $(COMPCERT)/Makefile.config
DIRS=lib common $(ARCH)/$(VARIANT) $(ARCH) backend cfrontend driver

INCLUDES=$(patsubst %,-I $(COMPCERT)/%, $(DIRS))

COQEXEC=coqtop -q $(INCLUDES) -I ../arm6 -I ../sh4 -R ../coq SimSoCCert -batch -load-vernac-source
#NAME=extract

ifeq ($(VERBOSE),1)
  SHOW := @true
  HIDE :=
else
  SHOW := @echo
  HIDE := @
endif

.PHONY: all extraction tags clean

all: extraction

extraction:
	$(SHOW) COQTOP extract/ExtractArm6_Sh4.v
	$(HIDE) mkdir -p tmp && \
	$(COQEXEC) ExtractArm6_Sh4.v 2>&1 > /dev/null

tags:
	otags -sr '.mli' -r .

clean:
	\rm -rf *~
