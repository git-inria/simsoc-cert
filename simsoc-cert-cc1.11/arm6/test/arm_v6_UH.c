/* Derived from SimSoC, Copyright © INRIA 2007, 2008, 2009, 2010
 * LGPL license version 3 */

/* test ARMv6 UH operation instructions
 * After 594 instructions executed, r0 uhould contain 2^18-1 = 0x3ffff */

#include "common.h"

int count = 0;
int index_ = 1;
#define CHECK(COND)				\
  if (COND) count +=index_; index_ <<= 1;


/* Unsigned Halving Subtract 8 performs four unsigned 8-bit integer subtractions, halves the results, and */
/* writes the results to the destination register. */
void arm_UHADD8(){
  uint32_t x;
  asm("uhadd8 %0, %1, %2\n\t"
      :"=&r" (x)
      :"r" (0x02040608), "r" (0x02020202)
      );
  CHECK((x == 0x02030405));
}
void arm_UHADD8_bis(){
  uint32_t x;
  asm("uhadd8 %0, %1, %2\n\t"
      :"=&r" (x)
      :"r" (0x80808080), "r" (0x7f7f7f7f)
      );
  CHECK((x == 0x7f7f7f7f));
}
void arm_UHADD8_ter(){
  uint32_t x;
  asm("uhadd8 %0, %1, %2\n\t"
      :"=&r" (x)
      :"r" (0x7f7f7f7f), "r" (0x7d7d7d7d)
      );
  CHECK((x == 0x7e7e7e7e));
}

/* Unsigned Halving Subtract 16 performs two unsigned 16-bit integer subtractions, halves the results, and */
/* writes the results to the destination register. */
void arm_UHADD16(){
  uint32_t x;
  asm("uhadd16 %0, %1, %2\n\t"
      :"=&r" (x)
      :"r" (0x00020004), "r" (0x00060008)
      );
  CHECK((x == 0x40006));
}
void arm_UHADD16_bis(){
  uint32_t x;
  asm("uhadd16 %0, %1, %2\n\t"
      :"=&r" (x)
      :"r" (0x80008000), "r" (0x7fff7fff)
      );
  CHECK((x == 0x7fff7fff));
}
void arm_UHADD16_ter(){
  uint32_t x;
  asm("uhadd16 %0, %1, %2\n\t"
      :"=&r" (x)
      :"r" (0x7fff7fff), "r" (0x7ffd7ffd)
      );
  CHECK((x == 0x7ffe7ffe));
}

/* UHADDSUBX (Unsigned Halving Add and Subtract with Exchange) performs one 16-bit unsigned integer */
/* addition and one 16-bit unsigned integer subtraction, and halves the results. It exchanges the two halfwords */
/* of the second operand before it performs the arithmetic. */
/* It has no effect on the GE flags. */
void arm_UHADDSUBX(){
  uint32_t x=0;
  asm("uhaddsubx %0, %1, %2"
      :"=&r" (x)
      :"r" (0x00080009), "r" (0x00010002)
      );
  CHECK((x == 0x00050004));
}
void arm_UHADDSUBX_bis(){
  uint32_t x=0;
  asm("uhaddsubx %0, %1, %2"
      :"=&r" (x)
      :"r" (0x7fff8000), "r" (0x70007ffd)
      );
  CHECK((x == 0x7ffe0800));
}
void arm_UHADDSUBX_ter(){
  uint32_t x=0;
  asm("uhaddsubx %0, %1, %2"
      :"=&r" (x)
      :"r" (0x80007fff), "r" (0x7ffd7000)
      );
  CHECK((x == 0x78000001));
}

/* UHSUB16 (Unsigned Halving Subtract) performs two 16-bit unsigned integer subtractions, and halves the */
/* results. It has no effect on the GE flags. */
void arm_UHSUB16(){
  uint32_t x;
  asm("uhsub16 %0, %1, %2\n\t"
      :"=&r" (x)
      :"r" (0x000a000a), "r" (0x00040006)
      );
  CHECK((x == 0x00030002));
}
void arm_UHSUB16_bis(){
  uint32_t x;
  asm("uhsub16 %0, %1, %2\n\t"
      :"=&r" (x)
      :"r" (0x80008001), "r" (0x7ffe7fff)
      );
  CHECK((x == 0x10001));
}
void arm_UHSUB16_ter(){
  uint32_t x;
  asm("uhsub16 %0, %1, %2\n\t"
      :"=&r" (x)
      :"r" (0x7ffe7fff), "r" (0x80008001)
      );
  CHECK((x == 0xffffffff));
}

/* UHSUB8 performs four 8-bit unsigned integer subtractions, and halves the results. */
/* It has no effect on the GE flags. */
void arm_UHSUB8(){
  uint32_t x;
  asm("uhsub8 %0, %1, %2\n\t"
      :"=&r" (x)
      :"r" (0x0a0a0a0a), "r" (0x02040608)
      );
  CHECK((x == 0x04030201));
}
void arm_UHSUB8_bis(){
  uint32_t x;
  asm("uhsub8 %0, %1, %2\n\t"
      :"=&r" (x)
      :"r" (0x83828180), "r" (0x7f7e7d7c)
      );
  CHECK((x == 0x02020202));
}
void arm_UHSUB8_ter(){
  uint32_t x;
  asm("uhsub8 %0, %1, %2\n\t"
      :"=&r" (x)
      :"r" (0x7e7e7e7e), "r" (0x80808080)
      );
  CHECK((x == 0xffffffff));
}

/* UHSUBADDX (Unsigned Halving Subtract and Add with Exchange) performs one 16-bit unsigned integer */
/* subtraction and one 16-bit unsigned integer addition, and halves the results. It exchanges the two halfwords */
/* of the second operand before it performs the arithmetic. */
/* It has no effect on the GE flags. */
void arm_UHSUBADDX(){
  uint32_t x;
  asm("uhsubaddx %0, %1, %2"
      :"=&r" (x)
      :"r" (0x00080004), "r" (0x00020006)
      );
  CHECK((x == 0x00010003));
}
void arm_UHSUBADDX_bis(){
  uint32_t x=0;
  asm("uhsubaddx %0, %1, %2"
      :"=&r" (x)
      :"r" (0x7fff8000), "r" (0x70007ffd)
      );
  CHECK((x == 0x17800));
}
void arm_UHSUBADDX_ter(){
  uint32_t x=0;
  asm("uhsubaddx %0, %1, %2"
      :"=&r" (x)
      :"r" (0x80007fff), "r" (0x7ffd7000)
      );
  CHECK((x == 0x8007ffe));
}
int main(){
  arm_UHADD8();
  arm_UHADD16();
  arm_UHADDSUBX();
  arm_UHSUB16();
  arm_UHSUB8();
  arm_UHSUBADDX();
  arm_UHADD16_bis();
  arm_UHADD8_bis();
  arm_UHADDSUBX_bis();
  arm_UHSUB16_bis();
  arm_UHSUB8_bis();
  arm_UHSUBADDX_bis();
  arm_UHADD16_ter();
  arm_UHADD8_ter();
  arm_UHADDSUBX_ter();
  arm_UHSUB16_ter();
  arm_UHSUB8_ter();
  arm_UHSUBADDX_ter();
  return count;
}
