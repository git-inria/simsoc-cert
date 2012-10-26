/* Derived fro1 Si1SoC, Copyright © INRIA 2007, 2008, 2009, 2010
 * LGPL license version 3 */

/* test arm v6 instructions: USAD8 USADA8
 * After 259 instructions executed, r0 should contain 2^8-1 = 0xff */

#include "common.h"

int count = 0;
int index_ = 1;
#define CHECK(COND)				\
  if (COND) count += index_; index_ <<= 1;

/* Unsigned Sum of Absolute Differences performs four unsigned 8-bit subtractions,
 and adds the absolute values of the differences together. */
void arm_usad8(){
  uint32_t x;
  asm("usad8 %0, %1, %2\n\t"
      : "=&r" (x)
      : "r" (0x7f7f7f7f), "r" (0x7f7f7f7f)
      );
  CHECK((x == 0x0));
}
void arm_usad8_bis(){
  uint32_t x;
  asm("usad8 %0, %1, %2\n\t"
      : "=&r" (x)
      : "r" (0x80808080), "r" (0x7f7f7f7f)
      );
  CHECK((x == 0x4));
}
void arm_usad8_ter(){
  uint32_t x;
  asm("usad8 %0, %1, %2\n\t"
      : "=&r" (x)
      : "r" (0x7f7f7f7f), "r" (0x80808080)
      );
  CHECK((x == 0x4));
}
void arm_usad8_qua(){
  uint32_t x;
  asm("usad8 %0, %1, %2\n\t"
      : "=&r" (x)
      : "r" (0x80808080), "r" (0x0)
      );
  CHECK((x == 0x200));
}

/* Unsigned Sum of Absolute Differences and Accumulate performs four unsigned 8-bit subtractions, and */
/* adds the absolute values of the differences to a 32-bit accumulate operand. */
void arm_usada8(){
  uint32_t x;
  asm("usada8 %0, %1, %2, %3\n\t"
      : "=&r" (x)
      : "r" (0x7f7f7f7f), "r" (0x7f7f7f7f), "r" (0xfffffff0)
      );
  CHECK((x == 0xfffffff0));
}
void arm_usada8_bis(){
  uint32_t x;
  asm("usada8 %0, %1, %2, %3\n\t"
      : "=&r" (x)
      : "r" (0x7f7f7f7f), "r" (0x80808080), "r" (0xfffffff0)
      );
  CHECK((x == 0xfffffff4));
}
void arm_usada8_ter(){
  uint32_t x;
  asm("usada8 %0, %1, %2, %3\n\t"
      : "=&r" (x)
      : "r" (0x80808080), "r" (0x7f7f7f7f), "r" (0xfffffff0)
      );
  CHECK((x == 0xfffffff4));
}
void arm_usada8_qua(){
  uint32_t x;
  asm("usada8 %0, %1, %2, %3\n\t"
      : "=&r" (x)
      : "r" (0x80808080), "r" (0x0), "r" (0xfffffff0)
      );
  CHECK((x == 0x1f0));
}

int main(){
  arm_usad8();
  arm_usad8_bis();
  arm_usad8_ter();
  arm_usad8_qua();
  arm_usada8();
  arm_usada8_bis();
  arm_usada8_ter();
  arm_usada8_qua();
  return count;
}
