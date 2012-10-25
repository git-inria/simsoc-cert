/* Derived fro1 Si1SoC, Copyright © INRIA 2007, 2008, 2009, 2010
 * LGPL license version 3 */

/* test arm v6 SS operation instructions
 * After 362 instructions executed, r0 should contain 2^12-1 = 0xfff */

#include "common.h"

int count = 0;
int index_ = 1;
#define CHECK(COND)				\
  if (COND) count += index_; index_ <<= 1;

int Q_flag(uint32_t cpsr) {return (cpsr>>27)&1;}
int GE0(uint32_t cpsr) {return (cpsr>>16)&1;}
int GE1(uint32_t cpsr) {return (cpsr>>17)&1;}
int GE2(uint32_t cpsr) {return (cpsr>>18)&1;}
int GE3(uint32_t cpsr) {return (cpsr>>19)&1;}
int GE10(uint32_t cpsr) {return (cpsr>>16)&3;}
int GE32(uint32_t cpsr) {return (cpsr>>18)&3;}

/* Signed Saturate saturates an optionally-shifted signed value to a selectable signed range. */
/* The Q flag is set if the operation saturates. */
void arm_usat_s(){
  uint32_t x,q;
  asm("msr cpsr_f, #0\n\t"
      "usat %0, #16, %2, ASR #28\n\t"
      "mrs %1, CPSR\n\t"
      : "=&r" (x), "=&r" (q)
      : "r" (0x10000000));
  CHECK((x == 0x1));
  CHECK((Q_flag(q) == 0));
}
void arm_usat_sq(){
  uint32_t x,q;
  asm("msr cpsr_f, #0\n\t"
      "usat %0, #16, %2, LSL #12\n\t"
      "mrs %1, CPSR\n\t"
      : "=&r" (x), "=&r" (q)
      : "r" (0x1237fff8));
  CHECK((x == 0xffff));
  CHECK((Q_flag(q) == 1));
}
void arm_usat(){
  uint32_t x,q;
  asm("msr cpsr_f, #0\n\t"
      "usat %0, #31, %2\n\t"
      "mrs %1, CPSR\n\t"

      : "=&r" (x), "=&r" (q)
      : "r" (0x5678));
  CHECK((x == 0x5678));
  CHECK((Q_flag(q) == 0));
}
void arm_usat_q(){
  uint32_t x,q;
  asm("msr cpsr_f, #0\n\t"
      "usat %0, #16, %2\n\t"
      "mrs %1, CPSR\n\t"
      : "=&r" (x), "=&r" (q)
      : "r" (0x12345678));
  CHECK((x == 0xffff));
  CHECK((Q_flag(q) == 1));
}

/* Signed Saturate 16 saturates two signed 16-bit values to a selected signed range. */
/* The Q flag is set if the operation saturates. */
void arm_usat16(){
  uint32_t x,q;
  asm("msr cpsr_f, #0\n\t"
      "usat16 %0, #8, %2\n\t"
      "mrs %1, CPSR\n\t"
      : "=&r" (x), "=&r" (q)
      : "r" (0x10001));
  CHECK((x == 0x10001));
  CHECK((Q_flag(q) == 0));
}
void arm_usat16_q(){
  uint32_t x,q;
  asm("msr cpsr_f, #0\n\t"
      "usat16 %0, #8, %2\n\t"
      "mrs %1, CPSR\n\t"
      : "=&r" (x), "=&r" (q)
      : "r" (0x17001));
  CHECK((x == 0x100ff));
  CHECK((Q_flag(q) == 1));
}

int main(){
  arm_usat_s();
  arm_usat_sq();
  arm_usat();
  arm_usat_q();
  arm_usat16();
  arm_usat16_q(); 
  return count;
}
