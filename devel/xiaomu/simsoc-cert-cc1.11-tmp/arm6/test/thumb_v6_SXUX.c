/* Derived from SimSoC, Copyright © INRIA 2007, 2008, 2009, 2010, 2011
 * LGPL license version 3 */

/* test thumb v6 instructions: SXTB, SXTH, UXTB, UXTH
 * After 590 instructions executed, r0 should contain 2^28-1 = 0xfffffff */

#include "common.h"

int count = 0;
int index_ = 1;
#define CHECK(COND)                         \
  if (COND) count+=index_; index_ <<= 1;

/* SXTB extracts an 8-bit value from a register and sign extends it to 32 bits.
 You can specify a rotation by 0, 8,16, or 24 bits before extracting the 8-bit value. */
void thumb_sxtb(){
  uint32_t x1,x2,x3,x4,x5,x6,x7;
  asm("sxtb %0, %1\n\t"
      : "=&r" (x1)
      : "r" (0x7f0180ff));
  asm("sxtb %0, %1\n\t"
      : "=&r" (x2)
      : "r" (0x7f01807f));
  asm("sxtb %0, %1\n\t"
      : "=&r" (x3)
      : "r" (0x7f018080));
  asm("sxtb %0, %1\n\t"
      : "=&r" (x4)
      : "r" (0x7f018000));
  asm("sxtb %0, %1\n\t"
      : "=&r" (x5)
      : "r" (0x7f018001));
  asm("sxtb %0, %1\n\t"
      : "=&r" (x6)
      : "r" (0x7f0180f0));
  asm("sxtb %0, %1\n\t"
      : "=&r" (x7)
      : "r" (0x7f01800f));
  CHECK((x1 == 0xffffffff));
  CHECK((x2 == 0x7f));
  CHECK((x3 == 0xffffff80));
  CHECK((x4 == 0x0));
  CHECK((x5 == 0x1));
  CHECK((x6 == 0xfffffff0));
  CHECK((x7 == 0xf));
}


/* Signed Extend Halfword extracts a 16-bit value from a register, sign-extends it to 32 bits, and writes the result */
/*  to the destination register. You can specify a rotation by 0, 8, 16, or 24 bits before extracting the 16-bit value. */
void thumb_sxth(){
  uint32_t f1,f2,f3,f4,f5,f6,f7;
  asm("sxth %0, %1\n\t"
      : "=&r" (f1)
      : "r" (0x7f017fff));
  asm("sxth %0, %1\n\t"
      : "=&r" (f2)
      : "r" (0x7f01ffff));
  asm("sxth %0, %1\n\t"
      : "=&r" (f3)
      : "r" (0x7f018000));
  asm("sxth %0, %1\n\t"
      : "=&r" (f4)
      : "r" (0x7f010000));
  asm("sxth %0, %1\n\t"
      : "=&r" (f5)
      : "r" (0x7f010001));
  asm("sxth %0, %1\n\t"
      : "=&r" (f6)
      : "r" (0x7f01f000));
  asm("sxth %0, %1\n\t"
      : "=&r" (f7)
      : "r" (0x7f010fff));
  CHECK((f1 == 0x7fff));
  CHECK((f2 == 0xffffffff));
  CHECK((f3 == 0xffff8000));
  CHECK((f4 == 0x0));
  CHECK((f5 == 0x1));
  CHECK((f6 == 0xfffff000));
  CHECK((f7 == 0xfff));
}

/* Unsigned Extend Byte extracts an 8-bit value from a register, zero-extends it to 32 bits, and writes the result */
/* to the destination register. You can specify a rotation by 0, 8, 16, or 24 bits before extracting the 8-bit value. */
void thumb_uxtb(){
  uint32_t x1,x2,x3,x4,x5,x6,x7;
  asm("uxtb %0, %1\n\t"
      : "=&r" (x1)
      : "r" (0x7f0180ff));
  asm("uxtb %0, %1\n\t"
      : "=&r" (x2)
      : "r" (0x7f01807f));
  asm("uxtb %0, %1\n\t"
      : "=&r" (x3)
      : "r" (0x7f018080));
  asm("uxtb %0, %1\n\t"
      : "=&r" (x4)
      : "r" (0x7f018000));
  asm("uxtb %0, %1\n\t"
      : "=&r" (x5)
      : "r" (0x7f018001));
  asm("uxtb %0, %1\n\t"
      : "=&r" (x6)
      : "r" (0x7f0180f0));
  asm("uxtb %0, %1\n\t"
      : "=&r" (x7)
      : "r" (0x7f01800f));
  CHECK((x1 == 0xff));
  CHECK((x2 == 0x7f));
  CHECK((x3 == 0x80));
  CHECK((x4 == 0x0));
  CHECK((x5 == 0x1));
  CHECK((x6 == 0xf0));
  CHECK((x7 == 0xf));
}
/* Unsigned Extend Halfword extracts a 16-bit value from a register, zero-extends it to 32 bits, and writes the */
/* result to the destination register. You can specify a rotation by 0, 8, 16, or 24 bits before extracting the 16-bit */
/* value. */
void thumb_uxth(){
  uint32_t f1,f2,f3,f4,f5,f6,f7;
  asm("uxth %0, %1\n\t"
      : "=&r" (f1)
      : "r" (0x7f017fff));
  asm("uxth %0, %1\n\t"
      : "=&r" (f2)
      : "r" (0x7f01ffff));
  asm("uxth %0, %1\n\t"
      : "=&r" (f3)
      : "r" (0x7f018000));
  asm("uxth %0, %1\n\t"
      : "=&r" (f4)
      : "r" (0x7f010000));
  asm("uxth %0, %1\n\t"
      : "=&r" (f5)
      : "r" (0x7f010001));
  asm("uxth %0, %1\n\t"
      : "=&r" (f6)
      : "r" (0x7f01f000));
  asm("uxth %0, %1\n\t"
      : "=&r" (f7)
      : "r" (0x7f010fff));
  CHECK((f1 == 0x7fff));
  CHECK((f2 == 0xffff));
  CHECK((f3 == 0x8000));
  CHECK((f4 == 0x0));
  CHECK((f5 == 0x1));
  CHECK((f6 == 0xf000));
  CHECK((f7 == 0xfff));
}

int main(){
  thumb_sxtb();
  thumb_sxth();
  thumb_uxtb();
  thumb_uxth();
  return count;
}
