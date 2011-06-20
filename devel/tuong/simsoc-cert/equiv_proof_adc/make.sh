#!/bin/bash
set -x
set -e

P=../
ARCH=`sed -n -e 's/^ARCH=//p' ${P}compcert/Makefile.config`
VARIANT=`sed -n -e 's/^VARIANT=//p' ${P}compcert/Makefile.config`

coqc \
  -I ${P}compcert/lib -I ${P}compcert/common -I ${P}compcert/$ARCH/$VARIANT -I ${P}compcert/$ARCH -I ${P}compcert/backend -I ${P}compcert/cfrontend \
  -I ${P}coq \
  -I ${P}arm6/coq \
  adc_compcert.v

coqc \
  -I ${P}compcert/lib -I ${P}compcert/common -I ${P}compcert/$ARCH/$VARIANT -I ${P}compcert/$ARCH -I ${P}compcert/backend -I ${P}compcert/cfrontend \
  -I ${P}coq \
  -I ${P}arm6/coq \
  theorem_equiv.v
