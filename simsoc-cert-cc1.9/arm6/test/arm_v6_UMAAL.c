/* Derived from SimSoC, Copyright © INRIA 2007, 2008, 2009, 2010
 * LGPL license version 3 */

/* test the ARM v6 instructions UMAAL
 * After 207 instructions executed, r0 uhould contain 2^8-1 = 0xff */

#include "common.h"

int count = 0;
int index_ = 1;
#define CHECK(COND)				\
  if (COND) count +=index_; index_ <<= 1;

/* Unsigned Multiply Accumulate Accumulate Long multiplies two unsigned 32-bit values to produce a 64-bit */
/* value, adds two unsigned 32-bit values, and writes the 64-bit result to two registers. */

void arm_UMAAL(){
  uint32_t dlo = 0x8, dhi=0x1;
  asm("umaal %0, %1, %2, %3"
      : "+&r" (dlo), "+&r" (dhi)
      : "r" (0xf), "r" (0xe)
      );
  CHECK((dlo == 0xdb));
  CHECK((dhi == 0x0));
}

void arm_UMAAL_bis(){
  uint32_t dlo = 0x12345678, dhi=0x87654321;
  asm("umaal %0, %1, %2, %3"
      : "+&r" (dlo), "+&r" (dhi)
      : "r" (0x13579bdf), "r" (0x02468ace)
      );
  CHECK((dlo == 0xc1193d0b));
  CHECK((dhi == 0x2c03a9));
}

void arm_UMAAL_ter(){
  uint32_t dlo = 0xffffffff, dhi=0xffffffff;
  asm("umaal %0, %1, %2, %3"
      : "+&r" (dlo), "+&r" (dhi)
      : "r" (0xffffffff), "r" (0xffffffff)
      );
  CHECK((dlo == 0xffffffff));
  CHECK((dhi == 0xffffffff));
}

void arm_UMAAL_qua(){
  uint32_t dlo = 0x0, dhi=0x0;
  asm("umaal %0, %1, %2, %3"
      : "+&r" (dlo), "+&r" (dhi)
      : "r" (0x0), "r" (0x1)
      );
  CHECK((dlo == 0x0));
  CHECK((dhi == 0x0));
}

int main(){
  arm_UMAAL();
  arm_UMAAL_bis();
  arm_UMAAL_ter();
  arm_UMAAL_qua();
  return count;
}
