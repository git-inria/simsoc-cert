// SimSoC-Cert, a library on processor architectures for embedded systems.
// See the COPYRIGHTS and LICENSE files.

// ISS for ARM processors implementing ARM architecture version 6.

// This file is used by the generated file "arm_iss.cpp"

#ifndef ARM_ISS_C_PRELUDE_H
#define ARM_ISS_C_PRELUDE_H

#include "arm_processor.hpp"
#include "arm_math.hpp"
#include "arm_not_implemented.hpp"
#include <assert.h>

// constants
static const uint8_t PC = 15;
static const uint8_t LR = 14;
static const uint8_t SP = 13;

// FIXME: not C
static uint32_t NOT(uint32_t x) {return ~x;}
static uint32_t NOT(bool x) {return !x;}

static bool not_cpy_instr(uint32_t bincode) {
  // values come from arm_iss.cpp, decode_and_exec method, case CPY
  return (bincode&0x0fff0ff0)!=0x01a00000;
}

// FIXME: not C
static uint64_t to_64(uint32_t x) {return static_cast<uint64_t>(x);}
static  int64_t to_64( int32_t x) {return static_cast< int64_t>(x);}
static uint64_t to_64(uint64_t x) {return x;}
static  int64_t to_64( int64_t x) {return x;}
static int16_t to_signed(uint16_t x) {return static_cast<int16_t>(x);}
static int32_t to_signed(uint32_t x) {return static_cast<int32_t>(x);}
static int64_t to_signed(uint64_t x) {return static_cast<int64_t>(x);}
static int16_t to_signed( int16_t x) {return x;}
static int32_t to_signed( int32_t x) {return x;}
static int64_t to_signed( int64_t x) {return x;}

#endif // ARM_ISS_C_PRELUDE_H
