/* Derived from SimSoC, Copyright © INRIA 2007, 2008, 2009, 2010
 * LGPL license version 3 */

/* test arm v6 instructions: SMMUL SMMLA SMMLS
 * After 193 instructions executed, r0 should contain 2^6-1 = 0x3f */

#include "common.h"

int count = 0;
int index_ = 1;
#define CHECK(COND)                         \
  if (COND) count+=index_; index_ <<= 1;

int Q_flag(uint32_t cpsr) {return (cpsr>>27)&1;}

/* Signed Most Significant Word Multiply multiplies two signed 32-bit values, extracts the most significant */
/* 32 bits of the result, and writes those bits to the destination register. */
void arm_SMMUL_R(){
  uint32_t x;
  asm("smmulr %0, %1, %2\n\t"
      :"=&r" (x)
      :"r" (0x60000000),"r" (0x4)
      );
  CHECK((x == 0x2));
}
void arm_SMMUL_T(){
  uint32_t x;
  asm("smmul %0, %1, %2\n\t"
      :"=&r" (x)
      :"r" (0x60000000),"r" (0x4)
      );
  CHECK((x == 0x1));
}

/* Signed Most Significant Word Multiply Accumulate multiplies two signed 32-bit values, extracts the most */
/* significant 32 bits of the result, and adds an accumulate value. */
void arm_SMMLA_R(){
  uint32_t x;
  asm("smmlar %0, %1, %2, %3\n\t"
      :"=&r" (x)
      :"r" (0xf0f0f0f0), "r" (0x12345678), "r" (0x114488bb)
      );
  CHECK((x == 0x10326587));
}
void arm_SMMLA_T(){
  uint32_t x;
  asm("smmla %0, %1, %2, %3\n\t"
      :"=&r" (x)
      :"r" (0xf0f0f0f0), "r" (0x12345678), "r" (0x114488bb)
      );
  CHECK((x == 0x10326586));
}

/* SMMLS (Signed Most significant word Multiply Subtract) multiplies two signed 32-bit values, extracts the */
/* most significant 32 bits of the result, and subtracts it from an accumulate value. */
void arm_SMMLS_R(){
  uint32_t x;
  asm("smmlsr %0, %1, %2, %3\n\t"
      :"=&r" (x)
      :"r" (0x7fff7fff),"r" (0x12345678), "r" (0x114488bb)
      );
  CHECK((x == 0x82a6699));
}
void arm_SMMLS_T(){
  uint32_t x;
  asm("smmls %0, %1, %2, %3\n\t"
      :"=&r" (x)
      :"r" (0xf0f0f0f0),"r" (0x12345678), "r" (0x114488bb)
      );
  CHECK((x == 0x1256abef));
}

int main(){
  arm_SMMUL_R();
  arm_SMMUL_T();
  arm_SMMLA_R();
  arm_SMMLA_T();
  arm_SMMLS_R();
  arm_SMMLS_T();

  return count;
}
