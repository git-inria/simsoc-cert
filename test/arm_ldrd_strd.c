/* Derived from SimSoC, Copyright © INRIA 2007, 2008, 2009, 2010
 * LGPL license version 3 */

/* test the LDRD and STRD instructions
 * After 181 instructions executed, r0 should contain 0xff = 255 */

#include "common.h"

int count = 0;

#define CHECK(ID, RESULT, EXPECTED)             \
  if ((RESULT)==(EXPECTED)) count+=(ID);

struct S {uint32_t words[2];} __attribute__ ((aligned (8)));
typedef struct S dword_t;

void test_ldrd_imm() {
  const dword_t in = {{0x12345678, 0x9abcdef0}};
  dword_t out = {{44,44}};

  if ((((int)&in)&0x10000007)!=0) {count = (int)&in; return;}
  if ((((int)&out)&0x10000007)!=0) {count = (int)&out; return;}

  asm("ldrd r4, [%2, #-4]\n\t"
      "mov %0, r4\n\t"
      "mov %1, r5"
      : "=r"(out.words[0]), "=r"(out.words[1])
      : "r"(&in.words[1]), "m"(in.words[0]), "m"(in.words[1])
      : "r4", "r5");
  CHECK(1, out.words[0], in.words[0]);
  CHECK(2, out.words[1], in.words[1]);
}

void test_ldrd_reg() {
  const dword_t in = {{0x12345678, 0x9abcdef0}};
  dword_t out = {{44,44}};
  asm("ldrd r4, [%2, %3]\n\t"
      "mov %0, r4\n\t"
      "mov %1, r5"
      : "=r"(out.words[0]), "=r"(out.words[1])
      : "r"(in.words+1), "r"(-4), "m"(in.words[0]), "m"(in.words[1])
      : "r4", "r5");
  CHECK(4, out.words[0], in.words[0]);
  CHECK(8, out.words[1], in.words[1]);
}

void test_strd_imm() {
  const dword_t in = {{0x12345678, 0x9abcdef0}};
  dword_t out  = {{44,44}};
  asm("mov r4, %0\n\t"
      "mov r5, %1\n\t"
      "strd r4, [%2, #-4]"
      :
      : "r"(in.words[0]), "r"(in.words[1]), "r"(out.words+1), "m"(out.words[0]), "m"(out.words[1])
      : "r4", "r5");
  CHECK(16, out.words[0], in.words[0]);
  CHECK(32, out.words[1], in.words[1]);
}

void test_strd_reg() {
  const dword_t in = {{0x12345678, 0x9abcdef0}};
  dword_t out = {{44,44}};
  asm("mov r4, %0\n\t"
      "mov r5, %1\n\t"
      "strd r4, [%2, %3]"
      :
      : "r"(in.words[0]), "r"(in.words[1]), "r"(out.words+1), "r"(-4), "m"(out.words[0]), "m"(out.words[1])
      : "r4", "r5");
  CHECK(64, out.words[0], in.words[0]);
  CHECK(128, out.words[1], in.words[1]);
}

int main() {
  test_ldrd_imm();
  test_strd_imm();
  test_ldrd_reg();
  test_strd_reg();
  return count;
}
