/* Derived from SimSoC, Copyright © INRIA 2007, 2008, 2009, 2010, 2011
 * LGPL license version 3 */

/* test the arm v6 instructions uqsub8, uqsub16, and uqsubADDX
 * After 760 instructions executed, r0 should contain 2^30-1 = 0x3fffffff */

#include "common.h"

int count = 0;
int index_ = 1;
#define CHECK(COND)				\
  if (COND) count +=index_; index_ <<= 1;

void arm_uqsub8(){
  uint32_t x1,x2,x3,x4,x5,x6,x7,x8,x9,x10;
  asm("uqsub8 %0, %1, %2\n\t"
      :"=&r" (x1)
      :"r" (0x0), "r" (0x80808080));
  asm("uqsub8 %0, %1, %2\n\t"
      :"=&r" (x2)
      :"r" (0x80808080), "r" (0x0)); 
  asm("uqsub8 %0, %1, %2\n\t"
      :"=&r" (x3)
      :"r" (0x2020202), "r" (0x80808080));
  asm("uqsub8 %0, %1, %2\n\t"
      :"=&r" (x4)
      :"r" (0x80808080), "r" (0x2020202));
  asm("uqsub8 %0, %1, %2\n\t"
      :"=&r" (x5)
      :"r" (0x7f7f7f7f), "r" (0x0));
  asm("uqsub8 %0, %1, %2\n\t"
      :"=&r" (x6)
      :"r" (0x0), "r" (0x7f7f7f7f));
  asm("uqsub8 %0, %1, %2\n\t"
      :"=&r" (x7)
      :"r" (0x7f7f7f7f), "r" (0x80808080));
  asm("uqsub8 %0, %1, %2\n\t"
      :"=&r" (x8)
      :"r" (0x80808080), "r" (0x7f7f7f7f));
  asm("uqsub8 %0, %1, %2\n\t"
      :"=&r" (x9)
      :"r" (0x3a3a3a3a), "r" (0x4f4f4f4f));
  asm("uqsub8 %0, %1, %2\n\t"
      :"=&r" (x10)
      :"r" (0x4f4f4f4f), "r" (0x3a3a3a3a));
  CHECK(x1 == 0x0);
  CHECK(x2 == 0x80808080);
  CHECK(x3 == 0x0);
  CHECK(x4 == 0x7e7e7e7e);
  CHECK(x5 == 0x7f7f7f7f);
  CHECK(x6 == 0x0);
  CHECK(x7 == 0x0);
  CHECK(x8 == 0x1010101);
  CHECK(x9 == 0x0);
  CHECK(x10 == 0x15151515);
}


void arm_uqsub16(){
  uint32_t x1,x2,x3,x4,x5,x6,x7,x8,x9,x10;
  asm("uqsub16 %0, %1, %2\n\t"
      :"=&r" (x1)
      :"r" (0x0), "r" (0x80008000));
  asm("uqsub16 %0, %1, %2\n\t"
      :"=&r" (x2)
      :"r" (0x80008000), "r" (0x0)); 
  asm("uqsub16 %0, %1, %2\n\t"
      :"=&r" (x3)
      :"r" (0x20002), "r" (0x80008000));
  asm("uqsub16 %0, %1, %2\n\t"
      :"=&r" (x4)
      :"r" (0x80008000), "r" (0x20002));
  asm("uqsub16 %0, %1, %2\n\t"
      :"=&r" (x5)
      :"r" (0x7fff7fff), "r" (0x0));
  asm("uqsub16 %0, %1, %2\n\t"
      :"=&r" (x6)
      :"r" (0x0), "r" (0x7fff7fff));
  asm("uqsub16 %0, %1, %2\n\t"
      :"=&r" (x7)
      :"r" (0x7fff7fff), "r" (0x80008000));
  asm("uqsub16 %0, %1, %2\n\t"
      :"=&r" (x8)
      :"r" (0x80008000), "r" (0x7fff7fff));
  asm("uqsub16 %0, %1, %2\n\t"
      :"=&r" (x9)
      :"r" (0x3aaa3aaa), "r" (0x4fff4fff));
  asm("uqsub16 %0, %1, %2\n\t"
      :"=&r" (x10)
      :"r" (0x4fff4fff), "r" (0x3aaa3aaa));
  CHECK(x1 == 0x0);
  CHECK(x2 == 0x80008000);
  CHECK(x3 == 0x0);
  CHECK(x4 == 0x7ffe7ffe);
  CHECK(x5 == 0x7fff7fff);
  CHECK(x6 == 0x0);
  CHECK(x7 == 0x0);
  CHECK(x8 == 0x10001);
  CHECK(x9 == 0x0);
  CHECK(x10 == 0x15551555);
}
void arm_uqsubaddx(){
  uint32_t x1,x2,x3,x4,x5,x6,x7,x8,x9,x10;
  asm("uqsubaddx %0, %1, %2\n\t"
      :"=&r" (x1)
      :"r" (0x0), "r" (0x80008000));
  asm("uqsubaddx %0, %1, %2\n\t"
      :"=&r" (x2)
      :"r" (0x80008000), "r" (0x0)); 
  asm("uqsubaddx %0, %1, %2\n\t"
      :"=&r" (x3)
      :"r" (0x20002), "r" (0x80008000));
  asm("uqsubaddx %0, %1, %2\n\t"
      :"=&r" (x4)
      :"r" (0x80008000), "r" (0x20002));
  asm("uqsubaddx %0, %1, %2\n\t"
      :"=&r" (x5)
      :"r" (0x7fff7fff), "r" (0x0));
  asm("uqsubaddx %0, %1, %2\n\t"
      :"=&r" (x6)
      :"r" (0x0), "r" (0x7fff7fff));
  asm("uqsubaddx %0, %1, %2\n\t"
      :"=&r" (x7)
      :"r" (0x7fff7fff), "r" (0x80008000));
  asm("uqsubaddx %0, %1, %2\n\t"
      :"=&r" (x8)
      :"r" (0x80008000), "r" (0x7fff7fff));
  asm("uqsubaddx %0, %1, %2\n\t"
      :"=&r" (x9)
      :"r" (0x3aaa4fff), "r" (0x4fff3aaa));
  asm("uqsubaddx %0, %1, %2\n\t"
      :"=&r" (x10)
      :"r" (0x4fff3aaa), "r" (0x3aaa4fff));
  CHECK(x1 == 0x8000);
  CHECK(x2 == 0x80008000);
  CHECK(x3 == 0x8002);
  CHECK(x4 == 0x7ffe8002);
  CHECK(x5 == 0x7fff7fff);
  CHECK(x6 == 0x7fff);
  CHECK(x7 == 0xffff);
  CHECK(x8 == 0x1ffff);
  CHECK(x9 == 0x9ffe);
  CHECK(x10 == 0x7554);
}


int main() {
  arm_uqsub8();
  arm_uqsub16();
  arm_uqsubaddx();
  return count;
}
