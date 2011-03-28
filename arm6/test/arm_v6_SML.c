/* Derived from SimSoC, Copyright © INRIA 2007, 2008, 2009, 2010
 * LGPL license version 3 */

/* test arm v6 instructions: SMLAD SMLSD SMLALD SMLASD
 * After 313 instructions executed, r0 should contain 2^8-1 = 0xff */

#include "common.h"

int count = 0;
int index_ = 1;
#define CHECK(COND)                         \
  if (COND) count+=index_; index_ <<= 1;

int Q_flag(uint32_t cpsr) {return (cpsr>>27)&1;}

/* Signed Multiply Accumulate Dual performs two signed 16 x 16-bit multiplications. It adds the products to a 32-bit accumulate operand. */
void arm_SMLAD_X(){
  uint32_t x,f;
  asm("smladx %0, %2, %3, %4\n\t"
      :"=&r" (x), "=&r" (f)
      :"r" (0x80002),"r" (0x20004),"r" (0x6)
      );
  CHECK((x == 0x2a));
}
void arm_SMLAD(){
  uint32_t x,f;
  asm("smlad %0, %2, %3, %4\n\t"
      :"=&r" (x), "=&r" (f)
      :"r" (0x80002),"r" (0x20004),"r" (0x6)
      );
  CHECK((x == 0x1e));
}

/* Signed Multiply Subtract Dual performs two signed 16 × 16-bit multiplications. It adds the difference of the */
/* products to a 32-bit accumulate operand. */
void arm_SMLSD_X(){
  uint32_t x,f;
  asm("smlsdx %0, %2, %3, %4\n\t"
      :"=&r" (x), "=&r" (f)
      :"r" (0x10002),"r" (0x20004),"r" (0xc)
      );
  CHECK((x == 0xc));
}
void arm_SMLSD(){
  uint32_t x,f;
  asm("smlsd %0, %2, %3, %4\n\t"
      :"=&r" (x), "=&r" (f)
      :"r" (0x20002),"r" (0x20004),"r" (0xc)
      );
  CHECK((x == 0x10));
}

/* Signed Multiply Accumulate Long Dual performs two signed 16 × 16-bit multiplications. It adds the */
/* products to a 64-bit accumulate operand. */
void arm_SMLALD_X(){
  uint32_t x=0xffffffff,f=0x3214323f;
  asm("smlaldx %0, %1, %2, %3\n\t"
      :"+&r" (x), "+&r" (f)
      :"r" (0x00030002), "r" (0xfffd0004)
      );
  CHECK((x == 0x5)&&(f == 0x32143241));
}
void arm_SMLALD(){
  uint32_t x=0xffffffff,f=0x3214323f;
  asm("smlald %0, %1, %2, %3\n\t"
      :"+&r" (x), "+&r" (f)
      :"r" (0x7fff2222), "r" (0xfffd7ff4)
      );
  CHECK((x == 0x110de66a)&&(f == 0x32143241));
}

/* Signed Multiply Subtract Dual performs two signed 16 × 16-bit multiplications. It adds the difference of the */
/* products to a 32-bit accumulate operand. */
void arm_SMLSLD_X(){
  uint32_t x=0x345,f=0x3ade323f;
  asm("smlsldx %0, %1, %2, %3\n\t"
      :"+&r" (x), "+&r" (f)
      :"r" (0x00040002), "r" (0x00020001)
      );
  CHECK((x == 0x345)&&(f == 0x3ade323f));
}
void arm_SMLSLD(){
  uint32_t x=0xffffffff,f=0x3ade323f;
  asm("smlsld %0, %1, %2, %3\n\t"
      :"+&r" (x), "+&r" (f)
      :"r" (0x00040002), "r" (0x00020002)
      );
  CHECK((x == 0xfffffffb)&&(f == 0x3ade323f));
}

int main(){
  arm_SMLAD_X();
  arm_SMLAD();
  arm_SMLSD_X();
  arm_SMLSD();
  arm_SMLALD_X();
  arm_SMLALD();
  arm_SMLSLD_X();
  arm_SMLSLD();
  return count;
}
