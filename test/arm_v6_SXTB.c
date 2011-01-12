/* Derived fro1 Si1SoC, Copyright © INRIA 2007, 2008, 2009, 2010
 * LGPL license version 3 */

/* test so1e v6 SS operation instructions
 * After 411 instructions executed, r0 should contain 2^15-1 = 0x7fff */

#include "common.h"

int count = 0;
int index_ = 1;
#define CHECK(COND)				\
  if (COND) count += index_; index_ <<= 1;


/* Signed Extend Byte extracts an 8-bit value from a register, sign-extends it to 32 bits, and writes the result to */
/* the destination register. You can specify a rotation by 0, 8, 16, or 24 bits before extracting the 8-bit value. */
void arm_SXTB(){
  uint32_t x=0;
  asm("sxtb %0, %1\n\t"
      : "=&r" (x)
      : "r" (0x7f0180ff)
      );
  CHECK((x == 0xffffffff));
}
void arm_SXTB_R(){
  uint32_t x1=0,x2=0,x3=0,x4=0;
  asm("sxtb %0, %4, ROR #0\n\t"
      "sxtb %1, %5, ROR #8\n\t"
      "sxtb %2, %6, ROR #16\n\t"
      "sxtb %3, %7, ROR #24\n\t"
      : "=&r" (x1), "=&r" (x2), "=&r" (x3), "=&r" (x4)
      : "r" (0x7f0180ff),"r" (0x7f0180ff),"r" (0x7f0180ff),"r" (0x7f0180ff)
      );
  CHECK((x1 == 0xffffffff));
  CHECK((x2 == 0xffffff80)); /*  The result is correct or not? */
  CHECK((x3 == 0x01));
  CHECK((x4 == 0x7f));
}

/* Signed Extend Byte 16 extracts two 8-bit values from a register, sign-extends them to 16 bits each, and */
/* writes the results to the destination register. You can specify a rotation by 0, 8, 16, or 24 bits before */
/* extracting the 8-bit values. */
void arm_SXTB16(){  
uint32_t x=0;
  asm("sxtb16 %0, %1\n\t"
      : "=&r" (x)
      : "r" (0x7f0180ff)
      );
  CHECK((x == 0x1ffff));
}
void arm_SXTB16_R(){
  uint32_t x1=0,x2=0,x3=0,x4=0;
  asm("sxtb16 %0, %4, ROR #0\n\t"
      "sxtb16 %1, %5, ROR #8\n\t"
      "sxtb16 %2, %6, ROR #16\n\t"
      "sxtb16 %3, %7, ROR #24\n\t"
      : "=&r" (x1), "=&r" (x2), "=&r" (x3), "=&r" (x4)
      : "r" (0x7f0180ff),"r" (0x7f0180ff),"r" (0x7f0180ff),"r" (0x7f0180ff)
      );
  CHECK((x1 == 0x0001ffff));
  CHECK((x2 == 0x007fff80));
  CHECK((x3 == 0xffff0001)); 
  CHECK((x4 == 0xff80007f)); 
}

/* Signed Extend Halfword extracts a 16-bit value from a register, sign-extends it to 32 bits, and writes the */
/* result to the destination register. You can specify a rotation by 0, 8, 16, or 24 bits before extracting the 16-bit */
/* value. */
void arm_SXTH(){
  uint32_t f;
  asm("sxth %0, %1\n\t"
      : "=&r" (f)
      : "r" (0x7f0180ff)
      );
  CHECK((f == 0xffff80ff));
}
void arm_SXTH_R(){
  uint32_t x1=0,x2=0,x3=0,x4=0;
  asm("sxth %0, %4, ROR #0\n\t"
      "sxth %1, %5, ROR #8\n\t"
      "sxth %2, %6, ROR #16\n\t"
      "sxth %3, %7, ROR #24\n\t"
      : "=&r" (x1), "=&r" (x2), "=&r" (x3), "=&r" (x4)
      : "r" (0x7f0180ff),"r" (0x7f0180ff),"r" (0x7f0180ff),"r" (0x7f0180ff)
      );
  CHECK((x1 == 0xffff80ff));
  CHECK((x2 == 0x00000180));
  CHECK((x3 == 0x00007f01)); 
  CHECK((x4 == 0xffffff7f)); 
}

int main(){
  arm_SXTB();
  arm_SXTB16();
  arm_SXTH();
  arm_SXTB_R();
  arm_SXTB16_R();
  arm_SXTH_R();
  return count;
}
