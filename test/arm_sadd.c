/* Derived from SimSoC, Copyright © INRIA 2007, 2008, 2009, 2010, 2011
 * LGPL license version 3 */

/* test the arm v6 instructions SADD8, SADD16, and SADDSUBX
 * After 655 instructions executed, r0 should contain 2^22-1 = 0x3fffff */

#include "common.h"

int count = 0;
int index_ = 1;

#define CHECK(COND)                         \
  if (COND) count+=index_; index_ <<= 1;

int GE0(uint32_t cpsr) {return (cpsr>>16)&1;}
int GE1(uint32_t cpsr) {return (cpsr>>17)&1;}
int GE2(uint32_t cpsr) {return (cpsr>>18)&1;}
int GE3(uint32_t cpsr) {return (cpsr>>19)&1;}
int GE10(uint32_t cpsr) {return (cpsr>>16)&3;}
int GE32(uint32_t cpsr) {return (cpsr>>18)&3;}

void arm_SADD8() {
  uint32_t result, cpsr;
  asm("sadd8 %0, %2, %3\n\t"
      "mrs %1, CPSR"
      : "=&r" (result), "=r" (cpsr)
      : "r" (0x026080fe), "r" (0x0360fffe));
  /* 1. case positive + positive -> positive: 0x02 + 0x03 = 0x05 */
  /* 2. case positive + positive -> positive (overflow): 0x60 + 0x60 = 0xc0 */
  /* 3. case negative + negative -> negative (overflow): 0x80 + 0xff = 0x7f */
  /* 4. case negative + negative -> negative: 0xfe + 0xfe = 0xfc */
  CHECK(result==0x05c07ffc);
  CHECK(GE3(cpsr)==1);
  CHECK(GE2(cpsr)==1);
  CHECK(GE1(cpsr)==0);
  CHECK(GE0(cpsr)==0);
}

void arm_SADD8_bis() {
  uint32_t result, cpsr;
  asm("sadd8 %0, %2, %3\n\t"
      "mrs %1, CPSR"
      : "=&r" (result), "=r" (cpsr)
      : "r" (0x02fe01fc), "r" (0xff04fe02));
  /* 5. case positive + negative -> positive: 0x02 + 0xff = 0x01 */
  /* 6. case negative + positive -> positive: 0xfe + 0x04 = 0x02 */
  /* 7. case positive + negative -> negative: 0x01 + 0xfe = 0xff */
  /* 8. case negative + positive -> negative: 0xfc + 0x02 = 0xfe */
  CHECK(result==0x0102fffe);
  CHECK(GE3(cpsr)==1);
  CHECK(GE2(cpsr)==1);
  CHECK(GE1(cpsr)==0);
  CHECK(GE0(cpsr)==0);
}

void arm_SADD16() {
  uint32_t result, cpsr;
  asm("sadd16 %0, %2, %3\n\t"
      "mrs %1, CPSR"
      : "=&r" (result), "=r" (cpsr)
      : "r" (0x0002fccc), "r" (0xffff0222));
  /* 1. case positive + negative -> positive: 0x0002 + 0xffff = 0x0001 */
  /* 2. case negative + positive -> negative: 0xfccc + 0x0222 = 0xfeee */
  CHECK(result==0x0001feee);
  CHECK(GE32(cpsr)==3);
  CHECK(GE10(cpsr)==0);
}

void arm_SADD16_bis() {
  uint32_t result, cpsr;
  asm("sadd16 %0, %2, %3\n\t"
      "mrs %1, CPSR"
      : "=&r" (result), "=r" (cpsr)
      : "r" (0x11116666), "r" (0x22227777));
  /* 3. case positive + positive -> positive: 0x1111 + 0x2222 = 0x3333 */
  /* 4. case positive + positive -> positive (overflow): 0x6666 + 0x7777 = 0xdddd */
  CHECK(result==0x3333dddd);
  CHECK(GE32(cpsr)==3);
  CHECK(GE10(cpsr)==3);
}

void arm_SADD16_ter() {
  uint32_t result, cpsr;
  asm("sadd16 %0, %2, %3\n\t"
      "mrs %1, CPSR"
      : "=&r" (result), "=r" (cpsr)
      : "r" (0xabcd8000), "r" (0xffffffff));
  /* 5. case negative + negative -> negative: 0xabcd + 0xffff = 0xabcc */
  /* 6. case negative + negative -> negative (overflow): 0x8000 + 0xffff = 0x7fff */
  CHECK(result==0xabcc7fff);
  CHECK(GE32(cpsr)==0);
  CHECK(GE10(cpsr)==0);
}

void arm_SADDSUBX() {
  uint32_t result, cpsr;
  asm("saddsubx %0, %2, %3\n\t"
      "mrs %1, CPSR"
      : "=&r" (result), "=r" (cpsr)
      : "r" (0xbeefcafe), "r" (0xcafefff1 /* NB: halfwords are permuted */));
  /* 1. case negative + negative -> negative: 0xbeef + 0xfff1 = 0xbee0 */
  /* 2. case positive - positive -> positive: 0xcafe + 0xcafe = 0 */
  CHECK(result==0xbee00000);
  CHECK(GE32(cpsr)==0);
  CHECK(GE10(cpsr)==3);
}

int main() {
  arm_SADD8();
  arm_SADD8_bis();
  arm_SADD16();
  arm_SADD16_bis();
  arm_SADD16_ter();
  arm_SADDSUBX();
  return count;
}
