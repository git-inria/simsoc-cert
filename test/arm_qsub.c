/* Derived from SimSoC, Copyright © INRIA 2007, 2008, 2009, 2010, 2011
 * LGPL license version 3 */

/* test the arm v6 instructions QSUB8, QSUB16, and QSUBADDX
 * After 106 instructions executed, r0 should contain 2^3-1 = 7 */

#include "common.h"

int count = 0;
int index_ = 1;
#define CHECK(COND)				\
  if (COND) count +=index_; index_ <<= 1;

void arm_QSUB8(){
  uint32_t x;
  asm("qsub8 %0, %1, %2\n\t"
      :"=&r" (x)
      :"r" (0xffffffff), "r" (0xffff0000));
  CHECK(x == 0x0000ffff);
}

void arm_QSUB16(){
  uint32_t x;
  asm("qsub16 %0, %1, %2\n\t"
      :"=&r" (x)
      :"r" (0xffffffff), "r" (0xffff0000));
  CHECK(x == 0x0000ffff);
}

void arm_QSUBADDX(){
  uint32_t x=0;
  asm("qsubaddx %0, %1, %2"
      :"=&r" (x)
      :"r" (0x0f0f0f0f), "r" (0x0f0f0f0f)
      );
  CHECK(x == 0x1e1e);
}

int main() {
  arm_QSUB8();
  arm_QSUB16();
  arm_QSUBADDX();
  return count;
}
