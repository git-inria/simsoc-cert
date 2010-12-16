/* Derived from SimSoC, Copyright © INRIA 2007, 2008, 2009, 2010
 * LGPL license version 3 */

/* test some multiplication instructions
 * After 227 instructions executed, r0 should contain 0x1ff = 511 */

#include "common.h"

int count = 0;

#define CHECK(ID, COND)                         \
  if (COND) count+=(ID);

void test_MULS() {
  uint32_t x, f;
  asm("muls %0, %2, %3\n\t"
      "mrs %1, CPSR"
      : "=&r" (x), "=r" (f)
      : "r" (4), "r" (5));
  CHECK(1,(x == 20)&&
        !(f&(1<<31))&&
        !(f&(1<<30)));
}

void test_MLAS() {
  uint32_t x, f;
  asm("mlas %0, %2, %3, %4\n\t"
      "mrs %1, CPSR"
      : "=&r" (x), "=r" (f)
      : "r" (4), "r" (5), "r" (1));
  CHECK(2,(x == 21)&&
        !(f&(1<<31))&&
        !(f&(1<<30)));
}

void test_UMULLS() {
  uint32_t x, y, f;
  asm("umulls %0, %1, %3, %4\n\t"
      "mrs %2, CPSR"
      : "=&r" (x), "=&r" (y), "=r" (f)
      : "r" (0x3c), "r" (0x40000002));
  CHECK(4,(y == 0xf)&&
        (x == 0x78)&&
        !(f&(1<<31))&&
        !(f&(1<<30)));
}

void test_UMLALS() {
  uint32_t x, y, f;
  x = 1;
  y = 2;
  asm("umlals %0, %1, %3, %4\n\t"
      "mrs %2, CPSR"
      : "+&r" (x), "+&r" (y), "=r" (f)
      : "r" (0x3c), "r" (0x40000002));
  CHECK(8,(x == 0x79)&&
        (y == 0x11)&&
        !(f&(1<<31))&&
        !(f&(1<<30)));
}

void test_SMULLS() {
  uint32_t x, y, f;
  asm("smulls %0, %1, %3, %4\n\t"
      "mrs %2, CPSR"
      : "=&r" (x), "=&r" (y), "=r" (f)
      : "r" (5), "r" (0xffffffff));
  CHECK(16,(x == 0xfffffffb)&&
        (y == 0xffffffff)&&
        (f&(1<<31))&&
        !(f&(1<<30)));
}

void test_SMLALS() {
  uint32_t x, y, cpsr;
  x = 1;
  y = 2;
  asm("smlals %0, %1, %3, %4\n\t"
      "mrs %2, CPSR"
      : "+&r" (x), "+&r" (y), "=r" (cpsr)
      : "r" (5), "r" (0xffffffff));
  CHECK(32,x == 0xfffffffc);
  CHECK(64,y == 0x1);
  CHECK(128, !(cpsr&(1<<31)));
  CHECK(256, !(cpsr&(1<<30)));
}

int main(){
  test_MULS();
  test_MLAS();
  test_UMULLS();
  test_UMLALS();
  test_SMULLS();
  test_SMLALS();
  return count;
}
