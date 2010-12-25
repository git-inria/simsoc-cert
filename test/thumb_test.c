/* Derived from SimSoC, Copyright © INRIA 2007, 2008, 2009, 2010
 * LGPL license version 3 */

/* test some instructions of the Thumb instruction set
 * After 368 instructions executed, r0 should contain 127 */

#include "common.h"
#include "string.h"

int count = 0;

#define CHECK(ID, COND)                         \
  if (COND) count+=(ID)

void test_add5() {
  uint32_t d,n;
  asm("add %0,pc,#1*4\n\t"
      "mov %1,pc"
      :"=r"(d), "=r" (n));
  CHECK(1, ((n+2)&~2)-2 == (d-4+2));
}

void test_asr1() {
  uint32_t m,n,d1,d2;
  m = 0xf0000000;
  n = 1;
  asm("asr %0,%1,#32"
      :"=r"(d1)
      :"r"(m));
  asm("asr %0,%1,#32"
      :"=r"(d2)
      :"r"(n));
  CHECK(2, (d1 == 0xffffffff) && (d2 == 0));
}

void test_asr2() {
  uint32_t d1,d2,d3,d4;

  // asr2 Rs[7:0] = 0
  d1 = 0xf;
  asm("asr %0 ,%1"
      :"+r" (d1)
      :"r" (0xf000));

  //asr2 Rs[7:0] < 32
  d2 = 0xf;
  asm("asr %0 ,%1"
      :"+r" (d2)
      :"r" (0x2));

  //asr2 Rs[7:0] >= 32
  d3 = 0xf;
  asm("asr %0 ,%1"
      :"+r" (d3)
      :"r" (0x21));
  d4 = 0xa0000000;
  asm("asr %0 ,%1"
      :"+r" (d4)
      :"r" (0x21));

  CHECK(4, (d1 == 0xf) && (d2 == 3) && (d3 == 0) && (d4 == 0xffffffff));
}

void test_ldr2_str2() {
  uint32_t d1;
  uint32_t m = 0xf0;
  uint32_t n = 0xaf0;
  uint32_t d = 0xffaaff;
  asm("str %0,[%1,%2]"
      :
      :"r"(d),"r"(m),"r"(n));
  asm("ldr %0,[%1,%2]"
      :"=r"(d1)
      :"r"(m),"r"(n));
  CHECK(8, d1 == 0xffaaff);
}

void test_ldrh2_strh2() {
  uint32_t d1;
  uint32_t m = 0xf2;
  uint32_t n = 0xaf2;
  uint32_t d = 0xaaff;
  asm("strh %0,[%1,%2]"
      :
      :"r"(d),"r"(m),"r"(n));
  asm("ldrh %0,[%1,%2]"
      :"=r"(d1)
      :"r"(m),"r"(n));
  CHECK(16, d1 == 0xaaff);
}

void test_ldrsb_ldrsh() {
  uint32_t d1,d2;
  uint32_t m = 0xf2;
  uint32_t n = 0xaf2;
  uint32_t d = 0xffff;
  asm("strb %0,[%1,%2]"
      :
      :"r"(d),"r"(m),"r"(n));
  asm("ldrsb %0,[%1,%2]"
      :"=r"(d1)
      :"r"(m),"r"(n));
  asm("strh %0,[%1,%2]"
      :
      :"r"(d),"r"(m),"r"(n));
  asm("ldrsh %0,[%1,%2]"
      :"=r"(d2)
      :"r"(m),"r"(n));
  CHECK(32, (d1 == 0xffffffff) && (d2 == 0xffffffff));
}

const char *hello_str = NULL;

void hello() {
  hello_str = "blx in thumb instructions test ok\n";
}

void test_blx() {
  asm("blx %0"
      :
      :"r" ((uint32_t)hello)
      :"lr");
  CHECK(64, hello_str &&
        !strcmp(hello_str, "blx in thumb instructions test ok\n"));
}

int main() {
  test_add5();
  test_asr1();
  test_asr2();
  test_ldr2_str2();
  test_ldrh2_strh2();
  test_ldrsb_ldrsh();
  test_blx();
  return count;
}
