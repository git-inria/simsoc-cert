/* Derived from SimSoC, Copyright © INRIA 2007, 2008, 2009, 2010, 2011
 * LGPL license version 3 */

/* test the arm v6 instructions QADD8, QADD16, and QADDSUBX
 * After ?? instructions executed, r0 should contain 2^13-1 = 0x1fff */

#include "common.h"

int count = 0;
int index_ = 1;

#define CHECK(COND)                             \
  if (COND) count+=index_; index_ <<= 1;

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

void arm_QADD16() {
  uint32_t x1,x2,x3,x4,x5,x6;

  asm("qadd16 %0, %1, %2\n\t"
      : "=&r" (x1)
      : "r" (0x00020004), "r" (0x00010001));
  CHECK(x1 == 0x30005);

  /* case: -2 + -3 = -5 = 0xfb */
  asm("qadd16 %0, %1, %2\n\t"
      : "=&r" (x2)
      : "r" (0xfffefffe), "r" (0xfffdfffd));
  CHECK(x2 == 0xfffbfffb);

  /* case: -10+8 = -2 = 0xfe */
  asm("qadd16 %0, %1, %2\n\t"
      : "=&r" (x3)
      : "r" (0xfff6fff6), "r" (0x080008));
  CHECK(x3 == 0xfffefffe);

  /* case: -10+12 = 2 = 0x02 */
  asm("qadd16 %0, %1, %2\n\t"
      : "=&r" (x4)
      : "r" (0xfff6fff6), "r" (0xc000c));
  CHECK(x4 == 0x020002);

  /* case: 127 + 127 = 127 = 0x7f */
  asm("qadd16 %0, %1, %2\n\t"
      : "=&r" (x5)
      : "r" (0x7fff7fff), "r" (0x7fff7fff));
  CHECK(x5 == 0x7fff7fff);

  /* case: -128 + -128 = -128 = 0x80 */
  asm("qadd16 %0, %1, %2\n\t"
      : "=&r" (x6)
      : "r" (0x80008000), "r" (0x80008000));
  CHECK(x6 == 0x80008000);
}

void arm_QADDSUBX(){
  uint32_t x=0;
  asm("qaddsubx %0, %1, %2"
      :"=&r" (x)
      :"r" (0x0f0f0f0f), "r" (0x0f0f0f0f));
  CHECK(x == 0x1e1e0000);
}

int main() {
  arm_QADD8();
  arm_QADD16();
  arm_QADDSUBX();
  return count;
}
