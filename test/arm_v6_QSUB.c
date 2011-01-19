/* Derived from SimSoC, Copyright © INRIA 2007, 2008, 2009, 2010, 2011
 * LGPL license version 3 */

/* test the arm v6 instructions QSUB8, QSUB16, and QSUBADDX
 * After ?? instructions executed, r0 should contain 2^ = 0x */

#include "common.h"

int count = 0;
int index_ = 1;
#define CHECK(COND)				\
  if (COND) count +=index_; index_ <<= 1;


/* Saturating Subtract 8 performs four 8-bit integer subtractions, saturates the results to the 8-bit signed integer */
/* range –2^7 ≤ x ≤ 2^7 – 1, and writes the results to the destination register. */
void arm_QSUB8(){
  uint32_t x1,x2,x3,x4,x5,x6,x7,x8,x9,x10;
  asm("qsub8 %0, %1, %2\n\t"
      :"=&r" (x1)
      :"r" (0x0), "r" (0x80808080));
  asm("qsub8 %0, %1, %2\n\t"
      :"=&r" (x2)
      :"r" (0x80808080), "r" (0x0)); 
  asm("qsub8 %0, %1, %2\n\t"
      :"=&r" (x3)
      :"r" (0x2020202), "r" (0x80808080));
  asm("qsub8 %0, %1, %2\n\t"
      :"=&r" (x4)
      :"r" (0x80808080), "r" (0x2020202));
  asm("qsub8 %0, %1, %2\n\t"
      :"=&r" (x5)
      :"r" (0x7f7f7f7f), "r" (0x0));
  asm("qsub8 %0, %1, %2\n\t"
      :"=&r" (x6)
      :"r" (0x0), "r" (0x7f7f7f7f));
  asm("qsub8 %0, %1, %2\n\t"
      :"=&r" (x7)
      :"r" (0x7f7f7f7f), "r" (0x80808080));
  asm("qsub8 %0, %1, %2\n\t"
      :"=&r" (x8)
      :"r" (0x80808080), "r" (0x7f7f7f7f));
  asm("qsub8 %0, %1, %2\n\t"
      :"=&r" (x9)
      :"r" (0x3a3a3a3a), "r" (0x4f4f4f4f));
  asm("qsub8 %0, %1, %2\n\t"
      :"=&r" (x10)
      :"r" (0x4f4f4f4f), "r" (0x3a3a3a3a));
  CHECK(x1 == 0x7f7f7f7f);
  CHECK(x2 == 0x80808080);
  CHECK(x3 == 0x7f7f7f7f);
  CHECK(x4 == 0x80808080);
  CHECK(x5 == 0x7f7f7f7f);
  CHECK(x6 == 0x81818181);
  CHECK(x7 == 0x7f7f7f7f);
  CHECK(x8 == 0x80808080);
  CHECK(x9 == 0xebebebeb);
  CHECK(x10 == 0x15151515);
}

/* Saturating Subtract 16 performs two 16-bit integer subtractions, saturates the results to the 16-bit signed */
/* integer range –2^15 ≤ x ≤ 2^15 – 1, and writes the results to the destination register. */
void arm_QSUB16(){
  uint32_t x1,x2,x3,x4,x5,x6,x7,x8,x9,x10;
  asm("qsub16 %0, %1, %2\n\t"
      :"=&r" (x1)
      :"r" (0x0), "r" (0x80008000));
  asm("qsub16 %0, %1, %2\n\t"
      :"=&r" (x2)
      :"r" (0x80008000), "r" (0x0)); 
  asm("qsub16 %0, %1, %2\n\t"
      :"=&r" (x3)
      :"r" (0x20002), "r" (0x80008000));
  asm("qsub16 %0, %1, %2\n\t"
      :"=&r" (x4)
      :"r" (0x80008000), "r" (0x20002));
  asm("qsub16 %0, %1, %2\n\t"
      :"=&r" (x5)
      :"r" (0x7fff7fff), "r" (0x0));
  asm("qsub16 %0, %1, %2\n\t"
      :"=&r" (x6)
      :"r" (0x0), "r" (0x7fff7fff));
  asm("qsub16 %0, %1, %2\n\t"
      :"=&r" (x7)
      :"r" (0x7fff7fff), "r" (0x80008000));
  asm("qsub16 %0, %1, %2\n\t"
      :"=&r" (x8)
      :"r" (0x80008000), "r" (0x7fff7fff));
  asm("qsub16 %0, %1, %2\n\t"
      :"=&r" (x9)
      :"r" (0x3aaa3aaa), "r" (0x4fff4fff));
  asm("qsub16 %0, %1, %2\n\t"
      :"=&r" (x10)
      :"r" (0x4fff4fff), "r" (0x3aaa3aaa));
  CHECK(x1 == 0x7fff7fff);
  CHECK(x2 == 0x80008000);
  CHECK(x3 == 0x7fff7fff);
  CHECK(x4 == 0x80008000);
  CHECK(x5 == 0x7fff7fff);
  CHECK(x6 == 0x80018001);
  CHECK(x7 == 0x7fff7fff);
  CHECK(x8 == 0x80008000);
  CHECK(x9 == 0xeaabeaab);
  CHECK(x10 == 0x15551555);
}

/* QSUBADDX (Saturating Subtract and Add with Exchange) performs one 16-bit signed integer addition and one */
/* 16-bit signed integer subtraction, saturating the results to the 16-bit signed integer range */
/* –2^15 ≤ x ≤ 2^15 – 1. It exchanges the two halfwords of the second operand before it performs the arithmetic. */
/* QSUBADDX does not affect any flags. */
void arm_QSUBADDX(){
  uint32_t x1,x2,x3,x4,x5,x6,x7,x8,x9,x10;
  asm("qsubaddx %0, %1, %2\n\t"
      :"=&r" (x1)
      :"r" (0x0), "r" (0x80008000));
  asm("qsubaddx %0, %1, %2\n\t"
      :"=&r" (x2)
      :"r" (0x80008000), "r" (0x0)); 
  asm("qsubaddx %0, %1, %2\n\t"
      :"=&r" (x3)
      :"r" (0x20002), "r" (0x80008000));
  asm("qsubaddx %0, %1, %2\n\t"
      :"=&r" (x4)
      :"r" (0x80008000), "r" (0x20002));
  asm("qsubaddx %0, %1, %2\n\t"
      :"=&r" (x5)
      :"r" (0x7fff7fff), "r" (0x0));
  asm("qsubaddx %0, %1, %2\n\t"
      :"=&r" (x6)
      :"r" (0x0), "r" (0x7fff7fff));
  asm("qsubaddx %0, %1, %2\n\t"
      :"=&r" (x7)
      :"r" (0x7fff7fff), "r" (0x80008000));
  asm("qsubaddx %0, %1, %2\n\t"
      :"=&r" (x8)
      :"r" (0x80008000), "r" (0x7fff7fff));
  asm("qsubaddx %0, %1, %2\n\t"
      :"=&r" (x9)
      :"r" (0x3aaa4fff), "r" (0x4fff3aaa));
  asm("qsubaddx %0, %1, %2\n\t"
      :"=&r" (x10)
      :"r" (0x4fff3aaa), "r" (0x3aaa4fff));
  CHECK(x1 == 0x7fff8000);
  CHECK(x2 == 0x80008000);
  CHECK(x3 == 0x7fff8002);
  CHECK(x4 == 0x80008002);
  CHECK(x5 == 0x7fff7fff);
  CHECK(x6 == 0x80017fff);
  CHECK(x7 == 0x7fffffff);
  CHECK(x8 == 0x8000ffff);
  CHECK(x9 == 0x7fff);
  CHECK(x10 == 0x7554);
}

int main() {
  arm_QSUB8();
  arm_QSUB16();
  arm_QSUBADDX();
  return count;
}
