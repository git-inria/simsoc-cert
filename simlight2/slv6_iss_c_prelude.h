/* SimSoC-Cert, a library on processor architectures for embedded systems. */
/* See the COPYRIGHTS and LICENSE files. */

/* ISS for ARM processors implementing ARM architecture version 6. */

/* This file is used by the generated file "slv6_iss*.c" */

#include "slv6_iss.h"
#include "slv6_processor.h"
#include "slv6_math.h"
#include "slv6_iss_expanded.h"
#include "slv6_iss_grouped.h"
#include "arm_not_implemented.h"

BEGIN_SIMSOC_NAMESPACE

/* constants */
static const uint8_t PC = 15;
static const uint8_t LR = 14;
static const uint8_t SP = 13;

static bool not_cpy_instr(uint32_t bincode) {
  /* values come from arm_iss.c, decode_and_exec method, case CPY */
  return (bincode&0x0fff0ff0)!=0x01a00000;
}

static bool not_AL_cond(SLv6_Condition cond) {
  return cond!=SLV6_AL;
}

static int8_t to_int8(uint8_t x) {return (int8_t)x;}
static int16_t to_int16(uint16_t x) {return (int16_t)x;}
static int32_t to_int32(uint32_t x) {return (int32_t)x;}
static int64_t to_int64(uint64_t x) {return (int64_t)x;}
static int64_t to_i64(uint32_t x) {return (int64_t)(int32_t)x;}
static uint64_t to_u64(uint32_t x) {return (uint64_t)x;}
