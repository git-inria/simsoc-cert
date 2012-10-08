/* Derived from SimSoC, Copyright © INRIA 2007, 2008, 2009, 2010, 2011
 * LGPL license version 3 */

/* test the arm v6 instructions UADD8, UADD16, and UADDSUBX
 * After 749 instructions executed, r0 should contain 2^25-1 = 0x1ffffff */

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

/* Unsigned Add 8 performs four unsigned 8-bit integer additions, and writes the results to the destination */
/* register. It sets the APSR.GE bits according to the results of the additions. */
void arm_UADD8() {
  uint32_t result, cpsr;
  asm("msr cpsr_s, #0\n\t"
      "uadd8 %0, %2, %3\n\t"
      "mrs %1, CPSR"
      : "=&r" (result), "=r" (cpsr)
      : "r" (0x026080fe), "r" (0x0360fffe));

  CHECK(result==0x05c07ffc);
  CHECK(GE3(cpsr)==0);
  CHECK(GE2(cpsr)==0);
  CHECK(GE1(cpsr)==1);
  CHECK(GE0(cpsr)==1);
}
void arm_UADD8_bis() {
  uint32_t result, cpsr;
  asm("msr cpsr_s, #0\n\t"
      "uadd8 %0, %2, %3\n\t"
      "mrs %1, CPSR"
      : "=&r" (result), "=r" (cpsr)
      : "r" (0x02fe01fc), "r" (0xff04fe02));

  CHECK(result==0x0102fffe);
  CHECK(GE3(cpsr)==1);
  CHECK(GE2(cpsr)==1);
  CHECK(GE1(cpsr)==0);
  CHECK(GE0(cpsr)==0);
}

/* Unsigned Add 16 performs two 16-bit unsigned integer additions, and writes the results to the destination */
/* register. It sets the APSR.GE bits according to the results of the additions. */
void arm_UADD16() {
  uint32_t result, cpsr;
  asm("msr cpsr_s, #0\n\t"
      "uadd16 %0, %2, %3\n\t"
      "mrs %1, CPSR"
      : "=&r" (result), "=r" (cpsr)
      : "r" (0x0002fccc), "r" (0xffff0222));

  CHECK(result==0x0001feee);
  CHECK(GE32(cpsr)==3);
  CHECK(GE10(cpsr)==0);
}

void arm_UADD16_bis() {
  uint32_t result, cpsr;
  asm("msr cpsr_s, #0\n\t"
      "uadd16 %0, %2, %3\n\t"
      "mrs %1, CPSR"
      : "=&r" (result), "=r" (cpsr)
      : "r" (0x11116666), "r" (0x22227777));

  CHECK(result==0x3333dddd);
  CHECK(GE32(cpsr)==0);
  CHECK(GE10(cpsr)==0);
}

void arm_UADD16_ter() {
  uint32_t result, cpsr;
  asm("msr cpsr_s, #0\n\t"
      "uadd16 %0, %2, %3\n\t"
      "mrs %1, CPSR"
      : "=&r" (result), "=r" (cpsr)
      : "r" (0xabcd8000), "r" (0xffffffff));

  CHECK(result==0xabcc7fff);
  CHECK(GE32(cpsr)==3);
  CHECK(GE10(cpsr)==3);
}

/* UADDSUBX (Unsigned Add and Subtract with Exchange) performs one 16-bit unsigned integer addition and */
/* one 16-bit unsigned integer subtraction. It exchanges the two halfwords of the second operand before it */
/* performs the arithmetic. It sets the GE bits in the CPSR according to the results of the addition and */
/* subtraction. */
void arm_UADDSUBX() {
  uint32_t result, cpsr;
  asm("msr cpsr_s, #0\n\t"
      "uaddsubx %0, %2, %3\n\t"
      "mrs %1, CPSR"
      : "=&r" (result), "=r" (cpsr)
      : "r" (0xbeefcafe), "r" (0xcafefff1 /* NB: halfwords are permuted */));

  CHECK(result==0xbee00000);
  CHECK(GE32(cpsr)==3);
  CHECK(GE10(cpsr)==0);
}
void arm_UADDSUBX_bis() {
  uint32_t result, cpsr;
  asm("msr cpsr_s, #0\n\t"
      "uaddsubx %0, %2, %3\n\t"
      "mrs %1, CPSR"
      : "=&r" (result), "=&r" (cpsr)
      : "r" (0x12345678), "r" (0x56781234)
      );
  CHECK(result==0x24680000);
  CHECK(GE32(cpsr)==0);
  CHECK(GE10(cpsr)==0);
}

int main() {
  arm_UADD8();
  arm_UADD8_bis();
  arm_UADD16();
  arm_UADD16_bis();
  arm_UADD16_ter();
  arm_UADDSUBX();
  arm_UADDSUBX_bis();
  return count;
}
