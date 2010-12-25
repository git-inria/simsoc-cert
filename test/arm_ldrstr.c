/* Derived from SimSoC, Copyright © INRIA 2007, 2008, 2009, 2010
 * LGPL license version 3 */

/* test the Load/Store instructions
 * After 486 instructions executed, r0 should contain 0x7ffffff */

#include "common.h"

int count = 0;

#define CHECK(ID, RESULT, EXPECTED)             \
  if ((RESULT)==(EXPECTED)) count+=(ID)

void test_offset_imm() {
  //[<Rn>, #+/- <offset_12>]!
  uint32_t x, y;
  asm("mov r0,#0x400\n\t"
      "str %2,[r0,#+0x400]!\n\t"
      "ldr %0,[%3,#+0x800]\n\t"
      "mov %1,r0"
      : "=r"(x), "=r"(y)
      : "r"(0xd000000e), "r"(0)
      : "r0");
  CHECK(1, x, 0xd000000e);
  CHECK(2, y, 0x800);
}

void test_offset_reg() {
  //[<Rn>,+/-<Rm>]!
  uint32_t a5=0x4000, x;
  asm("str %2,[%0,+%3]!\n\t"
      "ldr %1,[%4,+%0]"
      : "+&r"(a5), "=r"(x)
      : "r"(0xd000000e), "r"(0x4000), "r"(0));
  CHECK(4, x, 0xd000000e);
  CHECK(8, a5, 0x8000);
}

void test_offset_LSL_imm() {
  //[<Rn>,+/-<Rm>,<shift>#<shift_imm>]!
  //[<Rn>, +/- <Rm>,LSL#<shift_imm>]!
  uint32_t x, a1=0x120;
  asm("str %2,[%0,-%3,LSL#1]!\n\t"
      "ldr %1,[%4,#0x100]"
      : "+&r"(a1), "=r"(x)
      : "r"(0xd000000e), "r"(0x10), "r"(0));
  CHECK(16, x, 0xd000000e);
  CHECK(32, a1, 0x100);
}

void test_offset_LSR_imm() {
  //[<Rn>, +/- <Rm>,LSR#<shift_imm>]!
  uint32_t a1=0x120, x;
  asm("str %2,[%0,-%3,LSR#1]!\n\t"
      "ldr %1,[%4,#0x118]"
      : "+&r"(a1), "=r"(x)
      : "r"(0xd000000e), "r"(0x10), "r"(0));
  CHECK(64, x, 0xd000000e);
  CHECK(128, a1, 0x118);
}

void test_offset_ASR_imm() {
  //[<Rn>, +/- <Rm>,ASR#<shift_imm>]!
  uint32_t x, a1=0xe0000004;
  asm("str %2,[%0,-%3,ASR#2]!\n\t"
      "ldr %1,[%4,#0x4]"
      : "+&r"(a1), "=r"(x)
      : "r"(0xd000000e), "r"(0x80000000), "r"(0));
  CHECK(256, x, 0xd000000e);
  CHECK(512, a1, 0x4);
}

void test_offset_ROR_imm() {
  //[<Rn>, +/- <Rm>,ROR#<shift_imm>]!
  uint32_t x, a1=0xc0000004;
  asm("str %2,[%0,-%3,ROR#1]!\n\t"
      "ldr %1,[%4,+%5]"
      : "+&r"(a1), "=r"(x)
      : "r"(0xd000000e), "r"(0x7fff0009), "r"(0), "r"(0x8000));
  CHECK(1024, x, 0xd000000e);
  CHECK(2048, a1, 0x8000);
}

void test_offset_RRX() {
  //[<Rn>, +/- <Rm>,RRX]!
  uint32_t x, a1=0xc0000004;
  asm("msr CPSR_f, #0x20000000\n\t"
      "str %2,[%0,-%3,RRX]!\n\t"
      "ldr %1,[%4,%5]"
      : "+&r"(a1), "=r"(x)
      : "r"(0xd000000e), "r"(0x7fff0009), "r"(0), "r"(0x8000));
  CHECK(0x1000, x, 0xd000000e);
  CHECK(0x2000, a1, 0x8000);
}

void test_offset_imm_2() {
  //[<Rn>],#+/-<offset_12>
  uint32_t x, a1=0x120;
  asm("str %2,[%0],#+0x12\n\t"
      "ldr %1,[%3,#0x120]"
      : "+&r"(a1), "=r"(x)
      : "r"(0xd000000e), "r"(0));
  CHECK(0x4000, x, 0xd000000e);
  CHECK(0x8000, a1, 0x132);
}

void test_offset_reg_2() {
  //[<Rn>],+/-<Rm>
  uint32_t x, a1=0x120;
  asm("str %2,[%0],+%3\n\t"
      "ldr %1,[%4,#0x120]"
      : "+&r"(a1), "=r"(x)
      : "r"(0xd000000e), "r"(0x10), "r"(0));
  CHECK(0x10000, x, 0xd000000e);
  CHECK(0x20000, a1, 0x130);
}

void test_STRH() {
  //STRH
  uint32_t x;
  asm("str %3,[%3,#+0x20]\n\t"
      "strh %1,[%2,#+0xf]\n\t"
      "ldr %0,[%3,#+0x20]"
      : "=r"(x)
      : "r"(0xd000000a), "r"(0x11), "r"(0));
  CHECK(0x40000, x & 0x0000ffff, 0xa);
}

void test_LDRH() {
  //LDRH
  uint32_t x;
  asm("str %1,[%2,#+0x11]\n\t"
      "ldrh %0,[%3,#+0x20]"
      :"=r" (x)
      :"r"(0xddddaaaa), "r"(0xf), "r"(0));
  CHECK(0x80000, x, 0xaaaa);
}

void test_LDRSH() {
  //LDRSH
  uint32_t x;
  asm("str %1,[%2,#+0xf]\n\t"
      "ldrsh %0,[%3,#+0x20]"
      :"=r" (x)
      : "r"(0xee00), "r"(0x11), "r"(0));
  CHECK(0x100000, x, 0xffffee00);
}

void test_LDRSB() {
  //LDRSB
  uint32_t x;
  asm("str %1,[%2,#+0xf]\n\t"
      "ldrsb %0,[%3,#+0x20]"
      : "=r" (x)
      : "r"(0xeee0), "r"(0x11), "r"(0));
  CHECK(0x200000, x, 0xffffffe0);
}

void test_SWP() {
  //SWP
  uint32_t x, y;
  asm("str %2,[%3]\n\t"
      "swp %0,%4,[%3]\n\t"
      "ldr %1,[%3]"
      : "=&r"(x), "=r"(y)
      : "r"(0xd000000a), "r"(0x20), "r"(0xff));
  CHECK(0x400000, x, 0xd000000a);
  CHECK(0x800000, y, 0xff);
}

void test_SWPB() {
  //SWPB
  uint32_t x, y;
  asm("str %2,[%3]\n\t"
      "swpb %0,%4,[%3]\n\t"
      "ldrb %1,[%3]"
      : "=&r"(x), "=r"(y)
      : "r"(0xd000000a), "r"(0x20), "r"(0xff00));
  CHECK(0x1000000, x, 0xa);
  CHECK(0x2000000, y, 0x0);
}

void test_CLZ() {
  //CLZ
  uint32_t x;
  asm("clz %0,%1"
      : "=r"(x)
      : "r"(0xa));
  CHECK(0x4000000, x, 28);
}

int main() {
  test_offset_imm();
  test_offset_reg();
  test_offset_LSL_imm();
  test_offset_LSR_imm();
  test_offset_ASR_imm();
  test_offset_ROR_imm();
  test_offset_RRX();
  test_offset_imm_2();
  test_offset_reg_2();
  test_STRH();
  test_LDRH();
  test_LDRSH();
  test_LDRSB();
  test_SWP();
  test_SWPB();
  test_CLZ();
  return count;
}
