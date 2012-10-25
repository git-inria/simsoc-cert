/* Derived from SimSoC, Copyright © INRIA 2007, 2008, 2009, 2010
 * LGPL license version 3 */

/* test arm v6 instructions: SMUAD SMUSD
 * After ?? instructions executed, r0 should contain 2^20-1 = 0xfffff */

#include "common.h"

int count = 0;
int index_ = 1;
#define CHECK(COND)                         \
  if (COND) count+=index_; index_ <<= 1;

int Q_flag(uint32_t cpsr) {return (cpsr>>27)&1;}

/* Signed Dual Multiply Add performs two signed 16 × 16-bit multiplications. It adds the products together, */
/* and writes the result to the destination register. */
void arm_SMUAD_X(){
  uint32_t x1,x2,x3,x4,x5,x6,x7,q1,q2,q3,q4,q5,q6,q7;
  asm("msr cpsr_f, #0\n\t"
      "smuadx %0, %2, %3\n\t"
      "mrs %1, cpsr"
      :"=&r" (x1), "=&r" (q1)
      :"r" (0x00010002),"r" (0x00020004));
  asm("msr cpsr_f, #0\n\t"
      "smuadx %0, %2, %3\n\t"
      "mrs %1, cpsr"
      :"=&r" (x2), "=&r" (q2)
      :"r" (0x7fff8000),"r" (0x80007fff));  
  asm("msr cpsr_f, #0\n\t"
      "smuadx %0, %2, %3\n\t"
      "mrs %1, cpsr"
      :"=&r" (x3), "=&r" (q3)
      :"r" (0x7fff8000),"r" (0x7fff8000));
  asm("msr cpsr_f, #0\n\t"
      "smuadx %0, %2, %3\n\t"
      "mrs %1, cpsr"
      :"=&r" (x4), "=&r" (q4)
      :"r" (0x80007fff),"r" (0x80007fff));
  asm("msr cpsr_f, #0\n\t"
      "smuadx %0, %2, %3\n\t"
      "mrs %1, cpsr"
      :"=&r" (x5), "=&r" (q5)
      :"r" (0x80007fff),"r" (0x7fff8000));
  asm("msr cpsr_f, #0\n\t"
      "smuadx %0, %2, %3\n\t"
      "mrs %1, cpsr"
      :"=&r" (x6), "=&r" (q6)
      :"r" (0x7fff7fff),"r" (0x7fff7fff));
  asm("msr cpsr_f, #0\n\t"
      "smuadx %0, %2, %3\n\t"
      "mrs %1, cpsr"
      :"=&r" (x7), "=&r" (q7)
      :"r" (0x80008000),"r" (0x80008000));
  CHECK((x1 == 0x8)&&(Q_flag(q1)==0));
  CHECK((x2 == 0x7fff0001)&&(Q_flag(q2)==0));
  CHECK((x3 == 0x80010000)&&(Q_flag(q3)==0));
  CHECK((x4 == 0x80010000)&&(Q_flag(q4)==0));
  CHECK((x5 == 0x7fff0001)&&(Q_flag(q4)==0));
  CHECK((x6 == 0x7ffe0002)&&(Q_flag(q6)==0));
  CHECK((x7 == 0x80000000)&&(Q_flag(q7)==1));
}
void arm_SMUAD(){
  uint32_t x1,x2,x3,x4,x5,x6,x7,q1,q2,q3,q4,q5,q6,q7;
  asm("msr cpsr_f, #0\n\t"
      "smuad %0, %2, %3\n\t"
      "mrs %1, cpsr"
      :"=&r" (x1), "=&r" (q1)
      :"r" (0x00010002),"r" (0x00020004));
  asm("msr cpsr_f, #0\n\t"
      "smuad %0, %2, %3\n\t"
      "mrs %1, cpsr"
      :"=&r" (x2), "=&r" (q2)
      :"r" (0x7fff8000),"r" (0x80007fff));  
  asm("msr cpsr_f, #0\n\t"
      "smuad %0, %2, %3\n\t"
      "mrs %1, cpsr"
      :"=&r" (x3), "=&r" (q3)
      :"r" (0x7fff8000),"r" (0x7fff8000));
  asm("msr cpsr_f, #0\n\t"
      "smuad %0, %2, %3\n\t"
      "mrs %1, cpsr"
      :"=&r" (x4), "=&r" (q4)
      :"r" (0x80007fff),"r" (0x80007fff));
  asm("msr cpsr_f, #0\n\t"
      "smuad %0, %2, %3\n\t"
      "mrs %1, cpsr"
      :"=&r" (x5), "=&r" (q5)
      :"r" (0x80007fff),"r" (0x7fff8000));
  asm("msr cpsr_f, #0\n\t"
      "smuad %0, %2, %3\n\t"
      "mrs %1, cpsr"
      :"=&r" (x6), "=&r" (q6)
      :"r" (0x7fff7fff),"r" (0x7fff7fff));
  asm("msr cpsr_f, #0\n\t"
      "smuad %0, %2, %3\n\t"
      "mrs %1, cpsr"
      :"=&r" (x7), "=&r" (q7)
      :"r" (0x80008000),"r" (0x80008000));
  CHECK((x1 == 0xa)&&(Q_flag(q1)==0));
  CHECK((x2 == 0x80010000)&&(Q_flag(q2)==0));
  CHECK((x3 == 0x7fff0001)&&(Q_flag(q3)==0));
  CHECK((x4 == 0x7fff0001)&&(Q_flag(q4)==0));
  CHECK((x5 == 0x80010000)&&(Q_flag(q5)==0));
  CHECK((x6 == 0x7ffe0002)&&(Q_flag(q6)==0));
  CHECK((x7 == 0x80000000)&&(Q_flag(q7)==1));
}

/* Signed Dual Multiply Subtract performs two signed 16 × 16-bit multiplications. It subtracts one of the */
/* products from the other, and writes the result to the destination register. */
void arm_SMUSD_X(){
  uint32_t x1,x2,x3,x4,x5,x6,x7;
  asm("smusdx %0, %1, %2\n\t"
      :"=&r" (x1)
      :"r" (0x00040008),"r" (0x00030006));
  asm("smusdx %0, %1, %2\n\t"
      :"=&r" (x2)
      :"r" (0x7fff8000),"r" (0x80007fff));  
  asm("smusdx %0, %1, %2\n\t"
      :"=&r" (x3)
      :"r" (0x7fff8000),"r" (0x7fff8000));
  asm("smusdx %0, %1, %2\n\t"
      :"=&r" (x4)
      :"r" (0x80007fff),"r" (0x80007fff));
  asm("smusdx %0, %1, %2\n\t"
      :"=&r" (x5)
      :"r" (0x80007fff),"r" (0x7fff8000));
  asm("smusdx %0, %1, %2\n\t"
      :"=&r" (x6)
      :"r" (0x7fff7fff),"r" (0x7fff7fff));
  asm("smusdx %0, %1, %2\n\t"
      :"=&r" (x7)
      :"r" (0x80008000),"r" (0x80008000));
  CHECK((x1 == 0x0));
  CHECK((x2 == 0xffff));
  CHECK((x3 == 0x0));
  CHECK((x4 == 0x0));
  CHECK((x5 == 0xffff0001));
  CHECK((x6 == 0x0));
  CHECK((x7 == 0x0));
}
void arm_SMUSD(){
  uint32_t x1,x2,x3,x4,x5,x6,x7;
  asm("smusd %0, %1, %2\n\t"
      :"=&r" (x1)
      :"r" (0x00040008),"r" (0x00030006));
  asm("smusd %0, %1, %2\n\t"
      :"=&r" (x2)
      :"r" (0x7fff8000),"r" (0x80007fff));  
  asm("smusd %0, %1, %2\n\t"
      :"=&r" (x3)
      :"r" (0x7fff8000),"r" (0x7fff8000));
  asm("smusd %0, %1, %2\n\t"
      :"=&r" (x4)
      :"r" (0x80007fff),"r" (0x80007fff));
  asm("smusd %0, %1, %2\n\t"
      :"=&r" (x5)
      :"r" (0x80007fff),"r" (0x7fff8000));
  asm("smusd %0, %1, %2\n\t"
      :"=&r" (x6)
      :"r" (0x7fff7fff),"r" (0x7fff7fff));
  asm("smusd %0, %1, %2\n\t"
      :"=&r" (x7)
      :"r" (0x80008000),"r" (0x80008000));
  CHECK((x1 == 0x24));
  CHECK((x2 == 0x0));
  CHECK((x3 == 0xffff));
  CHECK((x4 == 0xffff0001));
  CHECK((x5 == 0x0));
  CHECK((x6 == 0x0));
  CHECK((x7 == 0x0));
}

int main(){
  arm_SMUAD_X();
  arm_SMUAD();
  arm_SMUSD_X();
  arm_SMUSD();
  return count;
}
