/* SimSoC-Cert, a library on processor architectures for embedded systems. */
/* See the COPYRIGHTS and LICENSE files. */

/* ISS for SH4 processors implementing SH4 architecture. */

/* This file is used by the generated file "slsh4_iss.c" */

#include "slsh4_processor.h"
#include "slsh4_math.h"
//#include "sh4_not_implemented.h"

BEGIN_SIMSOC_NAMESPACE

/* constants */
static const uint32_t FPSCR_MASK = 0x003FFFFF;
static const uint32_t H_00000100 = 256;

static int32_t to_signed(uint32_t x) {return x;}
