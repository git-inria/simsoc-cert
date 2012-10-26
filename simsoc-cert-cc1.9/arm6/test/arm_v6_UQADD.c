/* Derived from SimSoC, Copyright © INRIA 2007, 2008, 2009, 2010, 2011
 * LGPL license version 3 */

/* test the arm v6 instructions uqadd8, uqadd16, and uqaddsubx
 * After 487 instructions executed, r0 should contain 2^19-1 = 0x7ffff */

#include "common.h"

int count = 0;
int index_ = 1;

#define CHECK(COND)                             \
  if (COND) count+=index_; index_ <<= 1;

/* uqadd8 performs four 8-bit integer additions. It saturates the results to the 8-bit unsigned integer range 0 ≤ x ≤ 28 – 1. */
/* It has no effect on the GE flags. */
void arm_uqadd8() {
  uint32_t x1,x2,x3,x4,x5,x6;

  asm("uqadd8 %0, %1, %2\n\t"
      : "=&r" (x1)
      : "r" (0x01020304), "r" (0x01010101));
  CHECK(x1 == 0x02030405);

  /* case: 254 + 253 = 507 = 0x1fb */
  asm("uqadd8 %0, %1, %2\n\t"
      : "=&r" (x2)
      : "r" (0xfefefefe), "r" (0xfdfdfdfd));
  CHECK(x2 == 0xffffffff);

  /* case: 246 + 8 = 254 = 0xfe */
  asm("uqadd8 %0, %1, %2\n\t"
      : "=&r" (x3)
      : "r" (0xf6f6f6f6), "r" (0x08080808));
  CHECK(x3 == 0xfefefefe);

  /* case: 246 + 12 = 258 = 0x102 */
  asm("uqadd8 %0, %1, %2\n\t"
      : "=&r" (x4)
      : "r" (0xf6f6f6f6), "r" (0x0c0c0c0c));
  CHECK(x4 == 0xffffffff);

  /* case: 127 + 127 = 254 = 0xfe */
  asm("uqadd8 %0, %1, %2\n\t"
      : "=&r" (x5)
      : "r" (0x7f7f7f7f), "r" (0x7f7f7f7f));
  CHECK(x5 == 0xfefefefe);

  /* case: 128 + 128 = 256 = 0x100 */
  asm("uqadd8 %0, %1, %2\n\t"
      : "=&r" (x6)
      : "r" (0x80808080), "r" (0x80808080));
  CHECK(x6 == 0xffffffff);
}

/* uqadd16 (Unsigned Saturating Add) performs two 16-bit integer additions. It saturates the results to the 16-bit unsigned integer range 0 ≤ x ≤ 216 – 1. It has no effect on the GE flags. */
void arm_uqadd16() {
  uint32_t x1,x2,x3,x4,x5,x6;

  asm("uqadd16 %0, %1, %2\n\t"
      : "=&r" (x1)
      : "r" (0x00020004), "r" (0x1));
  CHECK(x1 == 0x20005);

  /* case1: 65534 + 65533 = 131067 = 0x1fffb */
  /* case2: 65534 + 65533 = 131067 = 0x1fffb */
  asm("uqadd16 %0, %1, %2\n\t"
      : "=&r" (x2)
      : "r" (0xfffefffe), "r" (0xfffdfffd));
  CHECK(x2 == 0xffffffff);

  /* case1: 65526 + 8 = 65534 = 0xfffe */
  /* case2: 65526 + 12 = 65538 = 0x10002 */
  asm("uqadd16 %0, %1, %2\n\t"
      : "=&r" (x3)
      : "r" (0xfff6fff6), "r" (0x8000c));
  CHECK(x3 == 0xfffeffff);

  /* case1: 65526 + 12 = 65538 = 0x10002 */
  /* case2: 65526 + 12 = 65538 = 0x10002 */
  asm("uqadd16 %0, %1, %2\n\t"
      : "=&r" (x4)
      : "r" (0xfff6fff6), "r" (0xc000c));
  CHECK(x4 == 0xffffffff);

  /* case1: 36863 + 36863 = 65534 = 0x11ffe */
  /* case2: 32767 + 32767 = 65534 = 0xfffe */
  asm("uqadd16 %0, %1, %2\n\t"
      : "=&r" (x5)
      : "r" (0x8fff7fff), "r" (0x8fff7fff));
  CHECK(x5 == 0xfffffffe);

  /* case1: 32768 + 32768 = 65536 = 0x10000 */
  /* case2: 32768 + 32768 = 65536 = 0x10000 */
  asm("uqadd16 %0, %1, %2\n\t"
      : "=&r" (x6)
      : "r" (0x80008000), "r" (0x80008000));
  CHECK(x6 == 0xffffffff);
}

/* uqaddSUBX (Unsigned Saturating Add and Subtract with Exchange) performs one 16-bit integer addition and */
/* one 16-bit subtraction. It saturates the results to the 16-bit unsigned integer range 0 ≤ x ≤ 216 – 1. It */
/* exchanges the two halfwords of the second operand before it performs the arithmetic.  */
/* It has no effect on the GE flags. */
void arm_uqaddsubx(){
  uint32_t x1,x2,x3,x4,x5,x6,x7;

 /* case1: 1 + 2 = 3 = 0x3 */
 /* case2: 3 - 4 = -1 = 0x0 */
  asm("uqaddsubx %0, %1, %2"
      :"=&r" (x1)
      :"r" (0x10003), "r" (0x40002));
  CHECK(x1 == 0x30000);

 /* case1: 1 + 4 = 5 = 0x5 */
 /* case2: 3 - 2 = 1 = 0x1 */
  asm("uqaddsubx %0, %1, %2"
      :"=&r" (x2)
      :"r" (0x10003), "r" (0x20004));
  CHECK(x2 == 0x50001);

 /* case1: 32768 + 32767 = 65535 = 0xffff */
 /* case2: 32767 - 32768 = -1 = 0x0 */
  asm("uqaddsubx %0, %1, %2"
      :"=&r" (x3)
      :"r" (0x80007fff), "r" (0x80007fff));
  CHECK(x3 == 0xffff0000);

 /* case1: 32767 + 32768 = 65535 = 0xffff */
 /* case2: 32768 - 32767 = 1 = 0x1 */
  asm("uqaddsubx %0, %1, %2"
      :"=&r" (x4)
      :"r" (0x7fff8000), "r" (0x7fff8000));
  CHECK(x4 == 0xffff0001);

 /* case1: 32767 + 32767 = 65534 = 0xfffe */
 /* case2: 32767 - 32767 = 0 = 0x0 */
  asm("uqaddsubx %0, %1, %2"
      :"=&r" (x5)
      :"r" (0x7fff7fff), "r" (0x7fff7fff));
  CHECK(x5 == 0xfffe0000);

 /* case1: 32768 + 32768 =  = 0x10000 */
 /* case2: 32767 - 32767 = 0 = 0x0 */
  asm("uqaddsubx %0, %1, %2"
      :"=&r" (x6)
      :"r" (0x80007fff), "r" (0x7fff8000));
  CHECK(x6 == 0xffff0000);

 /* case1: 32767 + 32767 = 65534 = 0xfffe */
 /* case2: 32768 - 32768 = 0 = 0x0 */
  asm("uqaddsubx %0, %1, %2"
      :"=&r" (x7)
      :"r" (0x7fff8000), "r" (0x80007fff));
  CHECK(x7 == 0xfffe0000);
}
int main() {
  arm_uqadd8();
  arm_uqadd16();
  arm_uqaddsubx();
  return count;
}
