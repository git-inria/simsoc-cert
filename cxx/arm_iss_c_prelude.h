/* SimSoC-Cert, a library on processor architectures for embedded systems. */
/* See the COPYRIGHTS and LICENSE files. */

/* ISS for ARM processors implementing ARM architecture version 6. */

/* This file is used by the generated file "arm_iss.c" */

#ifndef ARM_ISS_C_PRELUDE_H
#define ARM_ISS_C_PRELUDE_H

#include "arm_processor.h"
#include "arm_math.h"
#include "arm_not_implemented.h"
#include <assert.h>

/* constants */
static const uint8_t PC = 15;
static const uint8_t LR = 14;
static const uint8_t SP = 13;

static bool not_cpy_instr(uint32_t bincode) {
  /* values come from arm_iss.c, decode_and_exec method, case CPY */
  return (bincode&0x0fff0ff0)!=0x01a00000;
}

static int32_t to_int32(uint32_t x) {return (int32_t)x;}
static int64_t to_int64(uint64_t x) {return (int64_t)x;}
static int64_t to_i64(uint32_t x) {return (int64_t)(int32_t)x;}
static uint64_t to_u64(uint32_t x) {return (uint64_t)x;}

#endif /* ARM_ISS_C_PRELUDE_H */
