/* Derived from SimSoC, Copyright © INRIA 2007, 2008, 2009, 2010
 * LGPL license version 3 */

/* test some v6 new instructions
 * After ?? instructions executed, r0 should contain 2^15-1 = 0x7fff */

#include "common.h"

int count = 0;
int index_ = 1;
#define CHECK(COND)				\
  if (COND) count +=index_; index_ <<= 1;

int GE0(uint32_t cpsr) {return (cpsr>>16)&1;}
int GE1(uint32_t cpsr) {return (cpsr>>17)&1;}
int GE2(uint32_t cpsr) {return (cpsr>>18)&1;}
int GE3(uint32_t cpsr) {return (cpsr>>19)&1;}
int GE10(uint32_t cpsr) {return (cpsr>>16)&3;}
int GE32(uint32_t cpsr) {return (cpsr>>18)&3;}

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
  uint32_t x,ge,result;
  /* There is a bug here: the GE bits must be set to known values before 'sel' is
   * executed
   * Moreover, there is no reason to test the GE bits after. */ 
  asm("sadd8 %2, %5, %6\n\t"
      "sel %0, %3, %4\n\t"
      "mrs %1, cpsr\n\t"
      : "=&r" (x), "=&r" (ge), "=&r" (result)
      : "r" (0x12345678), "r" (0x87654321), "r" (0x026080fe), "r" (0x0360fffe));
  CHECK((x == 0x12344321)
  &&(GE3(ge)==1)
  &&(GE2(ge)==1)
  &&(GE1(ge)==0)
  &&(GE0(ge)==0)
  &&(result==0x05c07ffc));
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



int main() {
  arm_CPY();
  arm_CPS();
  arm_PKHBT();
  arm_PKHTB();
  arm_SEL();
  arm_SETEND_BE();
  arm_SETEND_LE();
  return count;
}
