/* Derived from SimSoC, Copyright © INRIA 2007, 2008, 2009, 2010
 * LGPL license version 3 */

/* test some v6 new instructions
 * After 820 instructions executed, r0 should contain 847139599 = 0x327e530f */

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

void arm1_QADD8() {//it can not deal with the negative numbers
  uint32_t x1,x2,x3,x4,x5,x6,x7,x8,x9;
  asm("qadd8 %0, %1, %2\n\t"
      : "=&r" (x1)
      : "r" (0x01020304), "r" (0x01010101));
  asm("qadd8 %0, %1, %2\n\t"
      : "=&r" (x2)
      : "r" (0x82828282), "r" (0x81828384));
/* the result is x2 == 0x7f7f7f7f, but x2 should be 0x83848586 */
  asm("qadd8 %0, %1, %2\n\t"
      : "=&r" (x3)
      : "r" (0x01020304), "r" (0x81818181));
/* the result is x3 == 0x7f7f7f7f, but x3 should be 0x00010203 */
  asm("qadd8 %0, %1, %2\n\t"
      : "=&r" (x4)
      : "r" (0x81818181), "r" (0x01020304)); 
/* the result is x4 == 0x7f7f7f7f, but x4 should be 0x00010203 */
  asm("qadd8 %0, %1, %2\n\t"
      : "=&r" (x5)

      : "r" (0x7f7f7f7f), "r" (0x7f7f7f7f));
  asm("qadd8 %0, %1, %2\n\t"
      : "=&r" (x6)
      : "r" (0xffffffff), "r" (0xffffffff)); 
/* the result is x6 == 0x7f7f7f7f, but x6 should be 0x80808080 */
  asm("qadd8 %0, %1, %2\n\t"
      : "=&r" (x7)
      : "r" (0x81018101), "r" (0x01810181));
/* the result is x7 == 0x7f7f7f7f, but x7 should be 0x0 */
  asm("qadd8 %0, %1, %2\n\t"
      : "=&r" (x8)
      : "r" (0x7fff7fff), "r" (0xff7fff7f));
/* the result is x8 == 0x7f7f7f7f, but x8 should be 0x0 */
  asm("qadd8 %0, %1, %2\n\t"
      : "=&r" (x9)
      : "r" (0xff7fff7f), "r" (0x7fff7fff)); 
/* he result is x9 == 0x7f7f7f7f, but x9 should be 0x0 */

  CHECK(64,(x1 == 0x2030405)
	&&(x2 == 0x7f7f7f7f)
	&&(x3 == 0x7f7f7f7f)
	&&(x4 == 0x7f7f7f7f)
	&&(x5 == 0x7fff7fff)
	&&(x6 == 0x7f7f7f7f)
	&&(x7 == 0x7f7f7f7f)
	&&(x8 == 0x7f7f7f7f)
	&&(x9 == 0x7f7f7f7f));
}

void arm1_QADD16() { //it can not deal with the negative numbers
  uint32_t x1,x2,x3,x4,x5,x6,x7,x8;
  asm("qadd16 %0, %1, %2\n\t"
      : "=&r" (x1)
      : "r" (0x00010003), "r" (0x00010003));
  asm("qadd16 %0, %1, %2\n\t"
      : "=&r" (x2)
      : "r" (0x800a8003), "r" (0x00018002));
/* the result is x2 == 0x7fff7fff, but x2 should be 0x80098005 */
  asm("qadd16 %0, %1, %2\n\t"
      : "=&r" (x3)
      : "r" (0x7fff0001), "r" (0x7fff0001));
  asm("qadd16 %0, %1, %2\n\t"
      : "=&r" (x4)
      : "r" (0x00017fff), "r" (0x00017fff));
  asm("qadd16 %0, %1, %2\n\t"
      : "=&r" (x5)
      : "r" (0x7fff7fff), "r" (0x7fff7fff));
  asm("qadd16 %0, %1, %2\n\t"
      : "=&r" (x6)
      : "r" (0xffffffff), "r" (0xffffffff));
/* the result is x6 == 0x7fff7fff, but x6 should be 0x80008000 */
  asm("qadd16 %0, %1, %2\n\t"
      : "=&r" (x7)
      : "r" (0x7fffffff), "r" (0x7fffffff));
/* the result is x7 == 0x7fff7fff, but x7 should be 0x7fff8000 */
  asm("qadd16 %0, %1, %2\n\t"
      : "=&r" (x8)
      : "r" (0xffff7fff), "r" (0xffff7fff));
/* the result is x8 == 0x7fff7fff, but x8 should be 0x7fff8000 */

  CHECK(128,(x1 == 0x20006)
	&&(x2 == 0x7fff7fff)
	&&(x3 == 0x7fff0002)
	&&(x4 == 0x27fff)
	&&(x5 == 0x7fff7fff)
	&&(x6 == 0x7fff7fff)
	&&(x7 == 0x7fff7fff)
	&&(x8 == 0x7fff7fff));
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

/* void arm1_LDREX() {               */
/*   uint32_t x; */
/*   asm("ldrex %0, %1\n\t" */
      
/*       : "=&r" (x) */
/*       : "r" (0x20)); */
/*   CHECK(1024,(x == 0x20)); */
/* } */

/* void arm1_STREX() {               */
/*   uint32_t x; */
/*   asm("strex %0, %1\n\t" */
      
/*       : "=&r" (x) */
/*       : "r" (0x20)); */
/*   CHECK(2048,(x == 0x20)); */
/* } */

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

void arm1_SADDSUBX() {
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

void arm1_SEL() {                
  uint32_t x, f;
  asm(
      "mrs %1, CPSR\n"
      "sel %0, %2, %3\n"
      : "=&r" (x), "=r" (f)
      : "r" (0x12345678), "r" (0x87654321));
  if(f&(1<<16))CHECK(65536,(x == 0x78));
          else CHECK(65536,(x == 0x21)); 
  if(f&(1<<17))CHECK(65536,(x == 0x56));
          else CHECK(65536,(x == 0x43));
  if(f&(1<<18))CHECK(65536,(x == 0x34));
          else CHECK(65536,(x == 0x65));
  if(f&(1<<19))CHECK(65536,(x == 0x12));
          else CHECK(65536,(x == 0x87));
}

void arm1_QADDSUBX(){
  uint32_t x=0;
    asm("qaddsubx %0, %1, %2"
	:"=&r" (x)
	:"r" (0x0f0f0f0f), "r" (0x0f0f0f0f)
	);
    CHECK(131072,(x == 0x1e1e0000));
}

void arm1_QSUBADDX(){
  uint32_t x=0;
    asm("qsubaddx %0, %1, %2"
	:"=&r" (x)
	:"r" (0x0f0f0f0f), "r" (0x0f0f0f0f)
	);
    CHECK(262144,(x == 0x1e1e));
}

void arm1_REV16(){
  uint32_t x=0;
    asm("rev16 %0, %1"
	:"=&r" (x)
	:"r" (0x12345678)
	);
    CHECK(524288,(x == 0x34127856));
}

void arm1_SETEND_BE(){
  uint32_t f;
    asm("setend be\n\t"
	"mrs %0, cpsr"
	:"=&r" (f)
	);
    f=(f&(1<<9))>>9;
    CHECK(1048576,(f == 1));
}

void arm1_SETEND_LE(){
  uint32_t f;
    asm("setend le\n\t"
	"mrs %0, cpsr"
	:"=&r" (f)
	);
    f=(f&(1<<9))>>9;
    CHECK(2097152,(f == 0));
}

void arm1_SHADD8(){
  uint32_t x;
    asm("shadd8 %0, %1, %2\n\t"
	:"=&r" (x)
	:"r" (0x12345678), "r" (0x87654321)
	);
    CHECK(4194304,(x == 0x4c4c4c4c));
}

void arm1_SHADD16(){
  uint32_t x;
    asm("shadd16 %0, %1, %2\n\t"
	:"=&r" (x)
	:"r" (0x12345678), "r" (0x87654321)
	);
    CHECK(8388608,(x == 0x4c4c4c4c));
}

void arm1_SHADDSUBX(){
  uint32_t x=0;
    asm("shaddsubx %0, %1, %2"
	:"=&r" (x)
	:"r" (0x0f0f0f0f), "r" (0x0f0f0f0f)
	);
    CHECK(16777216,(x == 0x1e1e0000));
}

void arm1_SHSUB16(){
  uint32_t x;
    asm("shsub16 %0, %1, %2\n\t"
	:"=&r" (x)
	:"r" (0x12345678), "r" (0x87654321)
	);
    CHECK(33554432,(x == 0xc56709ab));
}

void arm1_SHSUB8(){
  uint32_t x;
    asm("shsub8 %0, %1, %2\n\t"
	:"=&r" (x)
	:"r" (0x12345678), "r" (0x87654321)
	);
    CHECK(67108864,(x == 0xc56709ab));
}

void arm1_SHSUBADDX(){
  uint32_t x=0;
    asm("shsubaddx %0, %1, %2"
	:"=&r" (x)
	:"r" (0x0f0f0f0f), "r" (0x0f0f0f0f)
	);
    CHECK(134217728,(x == 0x1e1e));
}

void arm1_SMLAD(){
  uint32_t x,f;
  asm("smlad %0, %2, %3, %4\n\t"
      "mrs %1, cpsr"
      :"=&r" (x), "=&r" (f)
      :"r" (0x12345678),"r" (0x87654321),"r" (0x54326789)
      );
  CHECK(268435456,(x == 0x747f8f85)&&((f&(1<<27))==0));

}

void arm1_SMLSD(){
  uint32_t x,f;
  asm("smlsdx %0, %2, %3, %4\n\t"
      "mrs %1, cpsr"
      :"=&r" (x), "=&r" (f)
      :"r" (0x12345678),"r" (0x87654321),"r" (0xf1f1f1f1)
      );
  CHECK(536870912,(x == 0x1ae76295)&&((f&(1<<27))==0));
}

int main(){
  /* arm1_LDREX(); */
  /* arm1_STREX(); */
  arm1_SADD8();
  arm1_SADD16();
  arm1_REVSH();
  arm1_QSUB8();
  arm1_QSUB16();
  arm1_QADD8();
  arm1_QADD16();
  arm1_CPY();
  arm1_CPS();
  arm1_PKHBT();
  arm1_PKHTB();
  arm1_SADDSUBX();
  arm1_REV();
  arm1_SEL();
  arm1_QADDSUBX();
  arm1_QSUBADDX();
  arm1_REV16();
  arm1_SETEND_BE();
  arm1_SETEND_LE();
  arm1_SHADD8();
  arm1_SHADD16();
  arm1_SHADDSUBX();
  arm1_SHSUB8();
  arm1_SHSUB16();
  arm1_SHSUBADDX();
  arm1_SMLAD();
  arm1_SMLSD();
  return count;
}

