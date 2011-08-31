/* SimSoC-Cert, a library on processor architectures for embedded systems. */
/* See the COPYRIGHTS and LICENSE files. */

/* ISS for SH4 processors implementing SH4 architecture. */

/* This file is used by the generated file "slsh4_iss.c" */

#include "slsh4_processor.h"
#include "slsh4_math.h"
//#include "sh4_not_implemented.h"

BEGIN_SIMSOC_NAMESPACE

/* constants */
static const uint8_t DBR = 0;
static const uint8_t EXPEVT = 1;
static const uint8_t FPSCR_MASK = 2;
static const uint8_t FPSCR = 3;
static const uint8_t FPUL = 4;
static const uint8_t GBR = 5;
static const uint8_t H_00000100 = 6;
static const uint8_t MACH = 7;
static const uint8_t MACL = 8;
static const uint8_t PR = 9;
static const uint8_t SGR = 18;
static const uint8_t SPC = 19;
static const uint8_t SR = 20;
static const uint8_t SSR = 21;
static const uint8_t TRA = 22;
static const uint8_t VBR = 23;

static int32_t to_signed(uint32_t x) {return x;}
