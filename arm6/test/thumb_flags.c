/* Derived from SimSoC, Copyright © INRIA 2007, 2008, 2009, 2010
 * LGPL license version 3 */

/* test thumb-arm interworking
 * After 174 instructions executed, r0 should contain 2^5-1 = 31 */

#include "common.h"

int count = 0;
int index_ = 1;
#define CHECK(COND)                         \
  if (COND) count += index_; index_ <<= 1;

int N_flag(uint32_t cpsr) {return (cpsr>>31)&1;}
int Z_flag(uint32_t cpsr) {return (cpsr>>30)&1;}
int C_flag(uint32_t cpsr) {return (cpsr>>29)&1;}
int V_flag(uint32_t cpsr) {return (cpsr>>28)&1;}

void test_flags() {
  const uint32_t n = 0x40000001;
  uint32_t result, cpsr;
  asm ("add %0, %2, %3        \n\t"
       ".balign 4             \n\t"
       "mov     r0, pc        \n\t"
       "bx      r0            \n\t"
       ".code 32              \n\t"
       "mrs     %1, cpsr      \n\t"
       "add     r0, pc, #1    \n\t"
       "bx      r0            \n\t"
       ".code 16"
       : "=r"(result), "=r"(cpsr)
       : "r"(n), "r"(n)
       : "r0");
  CHECK(result==0x80000002);
  CHECK(N_flag(cpsr)==1);
  CHECK(Z_flag(cpsr)==0);
  CHECK(C_flag(cpsr)==0);
  CHECK(V_flag(cpsr)==1);
}

int main() {
  test_flags();
  return count;
}
