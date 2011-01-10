/* Derived from SimSoC, Copyright © INRIA 2007, 2008, 2009, 2010
 * LGPL license version 3 */

/* test some v6 new instructions
 * After ?? instructions executed, r0 should contain 2^15-1 = 0x7fff */

#include "common.h"

int count = 0;
int index_ = 1;
#define CHECK(COND)				\
  if (COND) count +=index_; index_ <<= 1;

void arm_SHADD8(){
  uint32_t x;
    asm("shadd8 %0, %1, %2\n\t"
	:"=&r" (x)
	:"r" (0x02040608), "r" (0x02020202)
	);
    CHECK((x == 0x02030405));
}

void arm_SHADD16(){
  uint32_t x;
    asm("shadd16 %0, %1, %2\n\t"
	:"=&r" (x)
	:"r" (0x00020004), "r" (0x00060008)
	);
    CHECK((x == 0x00040006));
}

void arm_SHADDSUBX(){
  uint32_t x=0;
    asm("shaddsubx %0, %1, %2"
	:"=&r" (x)
	:"r" (0x00080009), "r" (0x00010002)
	);
    CHECK((x == 0x00050004));
}

void arm_SHSUB16(){
  uint32_t x;
    asm("shsub16 %0, %1, %2\n\t"
	:"=&r" (x)
	:"r" (0x000a000a), "r" (0x00040006)
	);
    CHECK((x == 0x00030002));
}

void arm_SHSUB8(){
  uint32_t x;
    asm("shsub8 %0, %1, %2\n\t"
	:"=&r" (x)
	:"r" (0x0a0a0a0a), "r" (0x02040608)
	);
    CHECK((x == 0x04030201));
}

void arm_SHSUBADDX(){
  uint32_t x;
    asm("shsubaddx %0, %1, %2"
	:"=&r" (x)
	:"r" (0x00080004), "r" (0x00020006)
	);
    CHECK((x == 0x00010003));
}

int main(){
  arm_SHADD8();
  arm_SHADD16();
  arm_SHADDSUBX();
  arm_SHSUB8();
  arm_SHSUB16();
  arm_SHSUBADDX();
return count;
}
