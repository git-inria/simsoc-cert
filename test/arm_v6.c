/* Derived from SimSoC, Copyright © INRIA 2007, 2008, 2009, 2010
 * LGPL license version 3 */

/* test some v6 new instructions
 * After 821 instructions executed, r0 should contain 0x327e530f */

#include "common.h"

int count = 0;
int index_ = 1;
#define CHECK(COND)				\
  if (COND) count +=index_; index_ <<= 1;

void arm_REVSH() {
  uint32_t x;
  asm("revsh %0, %1\n\t"
      : "=&r" (x)
      : "r" (0x8765));
  CHECK((x == 0x6587));
}

void arm_REV() {
  uint32_t x;
  asm("rev %0, %1\n\t"
      
      : "=&r" (x)
      : "r" (0x11223344));
  CHECK((x == 0x44332211));
}

void arm_CPY() {
  uint32_t x;
  asm("cpy %0, %1\n\t"
      
      : "=&r" (x)
      : "r" (0x10101010));
  CHECK((x == 0x10101010));
}

void arm_CPS() {
  uint32_t f;
  asm("cpsie a, #31\n\t"
      "mrs %0, CPSR"
      : "=&r" (f)
      );
  CHECK(!(f&(1<<8))
	&&(f&(1<<7))
	&&(f& (1<<6))
	);
}

void arm_PKHBT() {
  uint32_t x;
  asm("pkhbt %0, %1, %2, lsl #1\n\t"
      
      : "=&r" (x)
      : "r" (0x0000ffff), "r" (0xffff0000));
  CHECK((x == 0xfffeffff));
}

void arm_PKHTB() {
  uint32_t x=0;
  asm("pkhtb %0, %1, %2, asr #1\n\t"
      
      : "=&r" (x)
      : "r" (0xff000000), "r" (0xff00));
  CHECK((x == 0xff007f80));
}

void arm_SEL() {
  uint32_t x,f;
  asm(
      "sel %0, %2, %3\n\t"
      "mrs %1, cpsr\n\t"
      : "=&r" (x), "=&r" (f)
      : "r" (0x12345678), "r" (0x87654321)
);
  CHECK((x == 0x12345678)
	&&(f&(1<<16))
	&&(f&(1<<17))
	&&(f&(1<<18))
	&&(f&(1<<19)));
}

void arm_REV16(){
  uint32_t x=0;
    asm("rev16 %0, %1"
	:"=&r" (x)
	:"r" (0x12345678)
	);
    CHECK((x == 0x34127856));
}

void arm_SETEND_BE(){
  uint32_t f;
    asm("setend be\n\t"
	"mrs %0, cpsr"
	:"=&r" (f)
	);
    f=(f&(1<<9))>>9;
    CHECK((f == 1));
}

void arm_SETEND_LE(){
  uint32_t f;
    asm("setend le\n\t"
	"mrs %0, cpsr"
	:"=&r" (f)
	);
    f=(f&(1<<9))>>9;
    CHECK((f == 0));
}

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

void arm_SMLAD(){
  uint32_t x,f;
  asm("smlad %0, %2, %3, %4\n\t"
      :"=&r" (x), "=&r" (f)
      :"r" (0x80002),"r" (0x20004),"r" (0x6)
      );
  CHECK((x == 0x1e));

}

void arm_SMLSD(){
  uint32_t x,f;
  asm("smlsdx %0, %2, %3, %4\n\t"
      :"=&r" (x), "=&r" (f)
      :"r" (0x10002),"r" (0x20004),"r" (0xc)
      );
  CHECK((x == 0xc));
}

int main() {
  arm_REVSH();
  arm_CPY();
  arm_CPS();
  arm_PKHBT();
  arm_PKHTB();
  arm_REV();
  arm_SEL();
  arm_REV16();
  arm_SETEND_BE();
  arm_SETEND_LE();
  arm_SHADD8();
  arm_SHADD16();
  arm_SHADDSUBX();
  arm_SHSUB8();
  arm_SHSUB16();
  arm_SHSUBADDX();
  arm_SMLAD();
  arm_SMLSD();
  return count;
}
