/* Derived from SimSoC, Copyright © INRIA 2007, 2008, 2009, 2010
 * LGPL license version 3 */

/* test v6 SM operation instructions
 * After 617 instructions executed, r0 should contain 2^18-1 = 0x3ffff */

#include "common.h"

int count = 0;
int index_ = 1;
#define CHECK(COND)                         \
  if (COND) count+=index_; index_ <<= 1;

int Q_flag(uint32_t cpsr) {return (cpsr>>27)&1;}

/* Signed Most Significant Word Multiply multiplies two signed 32-bit values, extracts the most significant */
/* 32 bits of the result, and writes those bits to the destination register. */
void arm_SMMUL_R(){
  uint32_t x;
  asm("smmulr %0, %1, %2\n\t"
      :"=&r" (x)
      :"r" (0x60000000),"r" (0x4)
      );
  CHECK((x == 0x2));
}
void arm_SMMUL_T(){
  uint32_t x;
  asm("smmul %0, %1, %2\n\t"
      :"=&r" (x)
      :"r" (0x60000000),"r" (0x4)
      );
  CHECK((x == 0x1));
}

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

/* Signed Most Significant Word Multiply Accumulate multiplies two signed 32-bit values, extracts the most */
/* significant 32 bits of the result, and adds an accumulate value. */
void arm_SMMLA_R(){
  uint32_t x;
  asm("smmlar %0, %1, %2, %3\n\t"
      :"=&r" (x)
      :"r" (0xf0f0f0f0), "r" (0x12345678), "r" (0x114488bb)
      );
  CHECK((x == 0x10326587));
}
void arm_SMMLA_T(){
  uint32_t x;
  asm("smmla %0, %1, %2, %3\n\t"
      :"=&r" (x)
      :"r" (0xf0f0f0f0), "r" (0x12345678), "r" (0x114488bb)
      );
  CHECK((x == 0x10326586));
}

/* SMMLS (Signed Most significant word Multiply Subtract) multiplies two signed 32-bit values, extracts the */
/* most significant 32 bits of the result, and subtracts it from an accumulate value. */
void arm_SMMLS_R(){
  uint32_t x;
  asm("smmlsr %0, %1, %2, %3\n\t"
      :"=&r" (x)
      :"r" (0x7fff7fff),"r" (0x12345678), "r" (0x114488bb)
      );
  CHECK((x == 0x82a6699));
}
void arm_SMMLS_T(){
  uint32_t x;
  asm("smmls %0, %1, %2, %3\n\t"
      :"=&r" (x)
      :"r" (0xf0f0f0f0),"r" (0x12345678), "r" (0x114488bb)
      );
  CHECK((x == 0x1256abef));
}

/* Signed Dual Multiply Add performs two signed 16 × 16-bit multiplications. It adds the products together, */
/* and writes the result to the destination register. */
void arm_SMUAD_X(){
  uint32_t x,q;
  asm("smuadx %0, %2, %3\n\t"
      "mrs %1, cpsr"
      :"=&r" (x), "=&r" (q)
      :"r" (0x00010002),"r" (0x00020004)
      );
  CHECK((x == 0x8));
}
void arm_SMUAD(){
  uint32_t x,q;
  asm("smuad %0, %2, %3\n\t"
      "mrs %1, cpsr"
      :"=&r" (x), "=&r" (q)
      :"r" (0x00010002),"r" (0x00020004)
      );
  CHECK((x == 0xa));
}

/* Signed Dual Multiply Subtract performs two signed 16 × 16-bit multiplications. It subtracts one of the */
/* products from the other, and writes the result to the destination register. */
void arm_SMUSD_X(){
  uint32_t x;
  asm("smusdx %0, %1, %2\n\t"
      :"=&r" (x)
      :"r" (0x00040008),"r" (0x00030006)
      );
  CHECK((x == 0x0));
}
void arm_SMUSD(){
  uint32_t x;
  asm("smusd %0, %1, %2\n\t"
      :"=&r" (x)
      :"r" (0x00040008),"r" (0x00030006)
      );
  CHECK((x == 0x24));
}

int main(){
  arm_SMMUL_R();
  arm_SMMUL_T();
  arm_SMLAD_X();
  arm_SMLAD();
  arm_SMLSD_X();
  arm_SMLSD();
  arm_SMLALD_X();
  arm_SMLALD();
  arm_SMLSLD_X();
  arm_SMLSLD();
  arm_SMMLA_R();
  arm_SMMLA_T();
  arm_SMMLS_R();
  arm_SMMLS_T();
  arm_SMUAD_X();
  arm_SMUAD();
  arm_SMUSD_X();
  arm_SMUSD();
  return count;
}
