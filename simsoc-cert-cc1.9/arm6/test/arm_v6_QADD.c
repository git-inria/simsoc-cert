/* Derived from SimSoC, Copyright © INRIA 2007, 2008, 2009, 2010, 2011
 * LGPL license version 3 */

/* test the arm v6 instructions QADD8, QADD16, and QADDSUBX
 * After 516 instructions executed, r0 should contain 2^19-1 = 0x7ffff */

#include "common.h"

int count = 0;
int index_ = 1;

#define CHECK(COND)                             \
  if (COND) count+=index_; index_ <<= 1;

/* QADD8 performs four 8-bit integer additions. It saturates the results to the 8-bit signed integer range */
/* –2^7 ≤ x ≤ 2^7 – 1. QADD8 does not affect any flags. */
void arm_QADD8() {
  uint32_t x1,x2,x3,x4,x5,x6;

  asm("qadd8 %0, %1, %2\n\t"
      : "=&r" (x1)
      : "r" (0x01020304), "r" (0x01010101));
  CHECK(x1 == 0x02030405);

  /* case: -2 + -3 = -5 = 0xfb */
  asm("qadd8 %0, %1, %2\n\t"
      : "=&r" (x2)
      : "r" (0xfefefefe), "r" (0xfdfdfdfd));
  CHECK(x2 == 0xfbfbfbfb);

  /* case: -10+8 = -2 = 0xfe */
  asm("qadd8 %0, %1, %2\n\t"
      : "=&r" (x3)
      : "r" (0xf6f6f6f6), "r" (0x08080808));
  CHECK(x3 == 0xfefefefe);

  /* case: -10+12 = 2 = 0x02 */
  asm("qadd8 %0, %1, %2\n\t"
      : "=&r" (x4)
      : "r" (0xf6f6f6f6), "r" (0x0c0c0c0c));
  CHECK(x4 == 0x02020202);

  /* case: 127 + 127 = 127 = 0x7f */
  asm("qadd8 %0, %1, %2\n\t"
      : "=&r" (x5)
      : "r" (0x7f7f7f7f), "r" (0x7f7f7f7f));
  CHECK(x5 == 0x7f7f7f7f);

  /* case: -128 + -128 = -128 = 0x80 */
  asm("qadd8 %0, %1, %2\n\t"
      : "=&r" (x6)
      : "r" (0x80808080), "r" (0x80808080));
  CHECK(x6 == 0x80808080);
}

/* QADD16 performs two 16-bit integer additions. It saturates the results to the 16-bit signed integer range */
/* –2^15 ≤ x ≤ 2^15 – 1. QADD16 does not affect any flags. */
void arm_QADD16() {
  uint32_t x1,x2,x3,x4,x5,x6;

  asm("qadd16 %0, %1, %2\n\t"
      : "=&r" (x1)
      : "r" (0x00020004), "r" (0x00010001));
  CHECK(x1 == 0x30005);

  /* case1: -2 + -3 = -5 => 0xfb */
  /* case2: -2 + -3 = -5 => 0xfb */
  asm("qadd16 %0, %1, %2\n\t"
      : "=&r" (x2)
      : "r" (0xfffefffe), "r" (0xfffdfffd));
  CHECK(x2 == 0xfffbfffb);

  /* case1: -10 + 8 = -2 => 0xfe */
  /* case2: -10 + 8 = -2 => 0xfe */
  asm("qadd16 %0, %1, %2\n\t"
      : "=&r" (x3)
      : "r" (0xfff6fff6), "r" (0x080008));
  CHECK(x3 == 0xfffefffe);

  /* case1: -10 + 12 = 2 => 0x02 */
  /* case2: -10 + 12 = 2 => 0x02 */
  asm("qadd16 %0, %1, %2\n\t"
      : "=&r" (x4)
      : "r" (0xfff6fff6), "r" (0xc000c));
  CHECK(x4 == 0x020002);

  /* case1: 32767 + 32767 = 65534 => 0x7fff */
  /* case2: 32767 + 32767 = 65534 => 0x7fff */
  asm("qadd16 %0, %1, %2\n\t"
      : "=&r" (x5)
      : "r" (0x7fff7fff), "r" (0x7fff7fff));
  CHECK(x5 == 0x7fff7fff);

  /* case1: -32768 + -32768 = -65536 => 0x8000 */
  /* case2: -32768 + -32768 = -65536 => 0x8000 */
  asm("qadd16 %0, %1, %2\n\t"
      : "=&r" (x6)
      : "r" (0x80008000), "r" (0x80008000));
  CHECK(x6 == 0x80008000);
}

/* QADDSUBX (Saturating Add and Subtract with Exchange) performs one 16-bit integer addition and one 16-bit */
/* subtraction. It saturates the results to the 16-bit signed integer range –2^15 ≤ x ≤ 2^15 – 1. QADDSUBX exchanges */
/* the two halfwords of the second operand before it performs the arithmetic. QADDSUBX does not affect any flags. */
void arm_QADDSUBX(){
  uint32_t x1,x2,x3,x4,x5,x6,x7;

 /* case1: 1 + 2 = 3 => 0x3 */
 /* case2: 3 - 4 = -1 => 0xffff */
  asm("qaddsubx %0, %1, %2"
      :"=&r" (x1)
      :"r" (0x10003), "r" (0x40002));
  CHECK(x1 == 0x3ffff);

 /* case1: 1 + 4 = 5 => 0x5 */
 /* case2: 3 - 2 = 1 => 0x1 */
  asm("qaddsubx %0, %1, %2"
      :"=&r" (x2)
      :"r" (0x10003), "r" (0x20004));
  CHECK(x2 == 0x50001);

 /* case1: -32768 + 32767 = -1 => 0xffff */
 /* case2: 32767 - -32768 = 65535 => 0x7fff */
  asm("qaddsubx %0, %1, %2"
      :"=&r" (x3)
      :"r" (0x80007fff), "r" (0x80007fff));
  CHECK(x3 == 0xffff7fff);

 /* case1: 32767 + -32768 = -1 => 0xffff */
 /* case2: -32768 - 32767 = -65535 => 0x8000 */
  asm("qaddsubx %0, %1, %2"
      :"=&r" (x4)
      :"r" (0x7fff8000), "r" (0x7fff8000));
  CHECK(x4 == 0xffff8000);

 /* case1: 32767 + 32767 = 65534 => 0x7fff */
 /* case2: 32767 - 32767 = 0 => 0x0 */
  asm("qaddsubx %0, %1, %2"
      :"=&r" (x5)
      :"r" (0x7fff7fff), "r" (0x7fff7fff));
  CHECK(x5 == 0x7fff0000);

 /* case1: -32768 + -32768 = -65536 => 0x8000 */
 /* case2: 32767 - 32767 = 0 => 0x0 */
  asm("qaddsubx %0, %1, %2"
      :"=&r" (x6)
      :"r" (0x80007fff), "r" (0x7fff8000));
  CHECK(x6 == 0x80000000);

 /* case1: 32767 + 32767 = 65534 => 0x7fff */
 /* case2: 32768 - 32768 = 0 => 0x0 */
  asm("qaddsubx %0, %1, %2"
      :"=&r" (x7)
      :"r" (0x7fff8000), "r" (0x80007fff));
  CHECK(x7 == 0x7fff0000);
}

int main() {
  arm_QADD8();
  arm_QADD16();
  arm_QADDSUBX();
  return count;
}
