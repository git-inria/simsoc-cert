/* Derived fro1 Si1SoC, Copyright © INRIA 2007, 2008, 2009, 2010
 * LGPL license version 3 */

/* test so1e v6 SS operation instructions
 * After 414 instructions executed, r0 should contain 2^15-1 = 0x7fff */

#include "common.h"

int count = 0;
int index_ = 1;
#define CHECK(COND)				\
  if (COND) count += index_; index_ <<= 1;

/* Signed Extend and Add Byte extracts an 8-bit value from a register, sign-extends it to 32 bits, adds the result */
/* to the value in another register, and writes the fina
l result to the destination register. You can specify a */
/* rotation by 0, 8, 16, or 24 bits before extracting the 8-bit value. */
void arm_SXTAB(){
  uint32_t x;
  asm("sxtab %0, %1, %2\n\t"
      : "=&r" (x)
      : "r" (0x01020304), "r" (0x05060708)
      );
  CHECK((x == 0x0102030c));
}
void arm_SXTAB_R(){
  uint32_t x1,x2,x3,x4;
  asm("sxtab %0, %1, %2, ROR #0\n\t"
      : "=&r" (x1)
      : "r" (0x01020304), "r" (0x05060708)
      );
  asm("sxtab %0, %1, %2, ROR #8\n\t"
      : "=&r" (x2)
      : "r" (0x01020304), "r" (0x05060708)
      );
  asm("sxtab %0, %1, %2, ROR #16\n\t"
      : "=&r" (x3)
      : "r" (0x01020304), "r" (0x05fa0708)
      );
  asm("sxtab %0, %1, %2, ROR #24\n\t"
      : "=&r" (x4)
      : "r" (0x01020304), "r" (0xfb060708)
      );
  CHECK((x1 == 0x0102030c));
  CHECK((x2 == 0x0102030b));
  CHECK((x3 == 0x010202fe));
  CHECK((x4 == 0x010202ff));
}

/* Signed Extend and Add Byte 16 extracts two 8-bit values from a register, sign-extends them to 16 bits each, */
/* adds the results to two 16-bit values from another register, and writes the final results to the destination */
/* register. You can specify a rotation by 0, 8, 16, or 24 bits before extracting the 8-bit values. */
void arm_SXTAB16(){
  uint32_t x;
  asm("sxtab16 %0, %1, %2\n\t"
      : "=&r" (x)
      : "r" (0x01020304), "r" (0x05060708)
      );
  CHECK((x == 0x0108030c));
}
void arm_SXTAB16_R(){
  uint32_t x1,x2,x3,x4;
  asm("sxtab16 %0, %1, %2, ROR #0\n\t"
      : "=&r" (x1)
      : "r" (0x01020304), "r" (0x05060708)
      );
  asm("sxtab16 %0, %1, %2, ROR #8\n\t"
      : "=&r" (x2)
      : "r" (0x01020304), "r" (0x05060708)
      );
  asm("sxtab16 %0, %1, %2, ROR #16\n\t"
      : "=&r" (x3)
      : "r" (0x01020304), "r" (0xfbfaf9f8)
      );
  asm("sxtab16 %0, %1, %2, ROR #24\n\t"
      : "=&r" (x4)
      : "r" (0x01020304), "r" (0xfbfaf9f8)
      );
  CHECK((x1 == 0x0108030c));
  CHECK((x2 == 0x0107030b));
  CHECK((x3 == 0x00fa02fe));
  CHECK((x4 == 0x00fb02ff));
}

/* Signed Extend and Add Halfword extracts a 16-bit value from a register, sign-extends it to 32 bits, adds the */
/* result to a value from another register, and writes the final result to the destination register. You can specify */
/* a rotation by 0, 8, 16, or 24 bits before extracting the 16-bit value. */
void arm_SXTAH(){
  uint32_t x;
  asm("sxtah %0, %1, %2\n\t"
      : "=&r" (x)
      : "r" (0x01020304), "r" (0x05060708)
      );
  CHECK((x == 0x01020a0c));
}
void arm_SXTAH_R(){
  uint32_t x1,x2,x3,x4;
  asm("sxtah %0, %1, %2, ROR #0\n\t"
      : "=&r" (x1)
      : "r" (0x01020304), "r" (0x05060708)
      );
  asm("sxtah %0, %1, %2, ROR #8\n\t"
      : "=&r" (x2)
      : "r" (0x01020304), "r" (0x05060708)
      );
  asm("sxtah %0, %1, %2, ROR #16\n\t"
      : "=&r" (x3)
      : "r" (0x01020304), "r" (0xfbfaf9f8)
      );
  asm("sxtah %0, %1, %2, ROR #24\n\t"
      : "=&r" (x4)
      : "r" (0x01020304), "r" (0xfbfaf9f8)
      );
  CHECK((x1 == 0x01020a0c));
  CHECK((x2 == 0x0102090b));
  CHECK((x3 == 0x0101fefe));
  CHECK((x4 == 0x0101fbff));
}

int main() {
  arm_SXTAB();
  arm_SXTAB_R();
  arm_SXTAB16();
  arm_SXTAB16_R();
  arm_SXTAH();
  arm_SXTAH_R();
  return count;
}
