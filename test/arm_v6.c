/* Derived from SimSoC, Copyright © INRIA 2007, 2008, 2009, 2010
 * LGPL license version 3 */

/* test some v6 new instructions
 * After ?? instructions executed, r0 should contain    = 0x530f */

#include "common.h"

int count = 0;

#define CHECK(ID, COND)                         \
  if (COND) count+=(ID)

void arm1_SADD8() {                         //EncodingA1 ARMv6*,ARMv7
  uint32_t x, f;
  asm("sadd8 %0, %2, %3\n\t"
      "mrs %1, CPSR"
      : "=&r" (x), "=r" (f)
      : "r" (0x12435687), "r" (0x12345678));
  CHECK(1,(x == 0x2477ACFF)
		&&(f&(1<<16))
		&&(f&(1<<17))
		&&(f&(1<<18))
		&&(f&(1<<19))
	);
}

void arm1_SADD16() {                        
  uint32_t x, f;
  asm("sadd16 %0, %2, %3\n\t"
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

void arm1_REVSH() {                 
  uint32_t x;
  asm("revsh %0, %1\n\t"
      : "=&r" (x)
      : "r" (0x8765));
  CHECK(4,(x == 0x6587));
}

void arm1_REV() {               
  uint32_t x;
  asm("rev %0, %1\n\t"
      
      : "=&r" (x)
      : "r" (0x11223344));
  CHECK(8,(x == 0x44332211));
}

void arm1_QSUB8(){                        
  uint32_t x;
  asm("qsub8 %0, %1, %2\n\t"
      :"=&r" (x)
      :"r" (0xffffffff), "r" (0xffff0000));

  CHECK(16,(x == 0x00007f7f));
}

void arm1_QSUB16(){                         
  uint32_t x;
  asm("qsub16 %0, %1, %2\n\t"
      :"=&r" (x)
      :"r" (0xffffffff), "r" (0xffff0000));

  CHECK(32,(x == 0x00007fff));
}

void arm1_QADD8() {                 
  uint32_t x;
  asm("qadd8 %0, %1, %2\n\t"
      : "=&r" (x)
      : "r" (0x0000fffe), "r" (0x00010001));

  CHECK(64,(x == 0x00017f7f));
}

void arm1_QADD16() {                
  uint32_t x;
  asm("qadd16 %0, %1, %2\n\t"
      
      : "=&r" (x)
      : "r" (0x4ffefffe), "r" (0x00010001));
  CHECK(128,(x == 0x4fff7fff));
}

void arm1_CPY() {              
  uint32_t x;
  asm("cpy %0, %1\n\t"
      
      : "=&r" (x)
      : "r" (0x10101010));
  CHECK(256,(x == 0x10101010));
}

void arm1_CPS() {                     
  uint32_t f;
  asm("cpsie a, #31\n\t"
      "mrs %0, CPSR"
      : "=&r" (f) 
      );
  CHECK(512, !(f&(1<<8))
	&&(f&(1<<7))
	&&(f& (1<<6))
	);
}
/*
void arm1_LDREX() {              
  uint32_t x;
  asm("ldrex %0, %1\n\t"
      
      : "=&r" (x)
      : "r" (0x20));
  CHECK(1024,(x == 0x20));
}
*/
/*
void arm1_STREX() {              
  uint32_t x;
  asm("strex %0, %1\n\t"
      
      : "=&r" (x)
      : "r" (0x20));
  CHECK(2048,(x == 0x20));
}
*/
void arm1_PKHBT() {              
  uint32_t x;
  asm("pkhbt %0, %1, %2, lsl #1\n\t"
      
      : "=&r" (x)
      : "r" (0x0000ffff), "r" (0xffff0000));
  CHECK(4096,(x == 0xfffeffff));
}

void arm1_PKHTB() {              
  uint32_t x=0;
  asm("pkhtb %0, %1, %2, asr #1\n\t"
      
      : "=&r" (x)
      : "r" (0xff000000), "r" (0xff00));
  CHECK(8192,(x == 0xff007f80));
}

void arm1_SADDSUBX() {//The pre-UAL syntax SADDSUBX<c> is equivalent to SASX<c>
  uint32_t x,f;
  asm("saddsubx %0, %2, %3\n\t"
      "mrs %1, CPSR"
      : "=&r" (x), "=&r" (f)
      : "r" (0x12345678), "r" (0x56781234)
      );
  CHECK(16384, (x == 0x24680000)
	&&(f&(1<<16))
	&&(f&(1<<17))
	&&(f&(1<<18))
	&&(f&(1<<19))
	);
}
/*There is a bug with this instruction*/
/*
void arm1_RFE() {
  uint32_t x;
  asm("RFEIA %0!\n\t"
      : "=&r" (x)
);
}
*/


int main(){
  arm1_SADD8();
  arm1_SADD16();
  arm1_REVSH();
  arm1_REV();
  arm1_QSUB8();
  arm1_QSUB16();
  arm1_QADD8();
  arm1_QADD16();
  arm1_CPY();
  arm1_CPS();
  // arm1_LDREX();
  // arm1_STREX();
  arm1_PKHBT();
  arm1_PKHTB();
  arm1_SADDSUBX();
  //arm1_RFE();

  return count;
}

