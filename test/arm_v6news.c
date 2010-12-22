/* Derived from SimSoC, Copyright © INRIA 2007, 2008, 2009, 2010
 * LGPL license version 3 */

/* test some v6 new instructions
 * After 9 instructions executed, r0 should contain 0x11f = 511 */

#include "common.h"

int count = 0;

#define CHECK(ID, COND)                         \
  if (COND) count+=(ID);

void arm_SASX() {
  uint32_t x, f;
  asm("sasx %0, %2, %3\n\t"
      "mrs %1, CPSR"
      : "=&r" (x), "=r" (f)
      : "r" (0x12345678), "r" (0x56781234));
  CHECK(1,(x == 0x24680000)
		&&(f&(1<<16))
		&&(f&(1<<17))
		&&(f&(1<<18))
		&&(f&(1<<19))
	);
}

void arm_SADD8() {
  uint32_t x, f;
  asm("sadd8 %0, %2, %3\n\t"
      "mrs %1, CPSR"
      : "=&r" (x), "=r" (f)
      : "r" (0x12435687), "r" (0x12345678));
  CHECK(2,(x == 0x2477ACFF)
		&&(f&(1<<16))
		&&(f&(1<<17))
		&&(f&(1<<18))
		&&(f&(1<<19))
	);
}

void arm_SADD16() {
  uint32_t x, f;
  asm("sadd16 %0, %2, %3\n\t"
      "mrs %1, CPSR"
      : "=&r" (x), "=r" (f)
      : "r" (0x12435687), "r" (0x12345678));
  CHECK(4,(x == 0x2477ACFF)
		&&(f&(1<<16))
		&&(f&(1<<17))
		&&(f&(1<<18))
		&&(f&(1<<19))
	);
}

void arm_REVSH() {
  uint32_t x;
  asm("revsh %0, %1\n\t"
      : "=&r" (x)
      : "r" (0x8765));
  CHECK(8,(x == 0x6587));
}

void arm_REV() {
  uint32_t x;
  asm("rev %0, %1\n\t"
      
      : "=&r" (x)
      : "r" (0x11223344));
  CHECK(16,(x == 0x44332211));
}

void arm_QSUB8(){
  uint32_t x;
  asm("qsub8 %0, %1, %2\n\t"
      :"=&r" (x)
      :"r" (0xffffffff), "r" (0xffff0000));//if you change %1, %2 with some other values, the return is not correct.

  CHECK(32,(x == 0x0000ffff));
}

void arm_QSUB16(){
  uint32_t x;
  asm("qsub16 %0, %1, %2\n\t"
      :"=&r" (x)
      :"r" (0xffffffff), "r" (0xffff0000));//if you change %1, %2 with some other values, the return is not correct.

  CHECK(64,(x == 0x0000ffff));
}

void arm_QADD8() {
  uint32_t x;
  asm("qadd8 %0, %1, %2\n\t"
      : "=&r" (x)
      : "r" (0x0000fffe), "r" (0x00010001));//if you change %1, %2 with some other values, the return is not correct.

  CHECK(128,(x == 0x0001ffff));
}

void arm_QADD16() {
  uint32_t x;
  asm("qadd16 %0, %1, %2\n\t"
      
      : "=&r" (x)
      : "r" (0x4ffeffff), "r" (0x00010001));//if you change %1, %2 with some other values, the return is not correct.
  CHECK(256,(x == 0x4fffffff));
}

int main(){
  arm_SASX();
  arm_SADD8();
  arm_SADD16();
  arm_REVSH();
  arm_REV();
  arm_QSUB8();
  arm_QSUB16();
  arm_QADD8();
  arm_QADD16();
  return count;
}

