/* Derived from SimSoC, Copyright © INRIA 2007, 2008, 2009, 2010
 * LGPL license version 3 */

/* test the main data processing instructions
 * After 964 instructions executed, r0 should contain 0x7ffff = 524287 */

#include "common.h"

int count = 0;

void test_LSL_shift_imm() {
  uint32_t x;
  asm("mov r0,#0xf");
  asm("mov %0,r0,LSL #2"
      : "=r" (x));
  if (x==60) count+=1;
}

void test_LSR_shift_imm() {
  uint32_t y;
  asm("mov r0, #0xf");
  asm("mov %0,r0, LSR #2"
      : "=r" (y));
  if (y==3) count+=2;
}

void test_ASR_shift_imm() {
  uint32_t z;
  asm("mov r0, #0x80000000");
  asm("mov %0,r0, ASR #2"
      : "=r" (z));
  if (z==0xe0000000) count+=4;
}

void test_ROR_shift_imm() {
  uint32_t a;
  asm("mov r0, #0xf");
  asm("mov %0,r0, ROR #2"
      : "=r" (a));
  if (a==0xc0000003) count+=8;
}

void test_LSL_reg() {
  uint32_t b;
  asm("mov r0, #0xf");
  asm("mov r1, #2");
  asm("mov %0,r0, LSL r1"
      : "=r" (b));
  if (b==60) count+=16;
}

void test_LSR_reg() {
  uint32_t c;
  asm("mov r0, #0xf");
  asm("mov r1, #2");
  asm("mov %0,r0, LSR r1"
      : "=r" (c));
  if (c==3) count+=32;
}

void test_ASR_reg() {
  uint32_t d;
  asm("mov r0, #0x80000000");
  asm("mov r1, #2");
  asm("mov %0,r0, ASR r1"
      : "=r" (d));
  if (d==0xe0000000) count+=64;
}

void test_ROR_reg() {
  uint32_t e;
  asm("mov r0, #0xf");
  asm("mov r1, #2");
  asm("mov %0,r0, ROR r1"
      : "=r" (e));
  if (e==0xc0000003) count+=128;
}

void test_RRX() {
  uint32_t g;
  asm("mov r0, #0xe");
  asm("movs %0,r0, RRX"
      : "=r" (g));
  if (g==0x80000007) count+=256;
}

void test_EORS() {
  uint32_t rd, cpsr;
  uint32_t two = 2;
  asm ("msr CPSR_f, #0xf0000000\n\t"
       "EORs %0,%2,#1\n\t"
       "mrs %1,CPSR"
       : "=r" (rd), "=r" (cpsr)
       : "r" (two));
  if (rd==3 &&
      get_N_flag(cpsr)==0 &&
      get_Z_flag(cpsr)==0 &&
      get_C_flag(cpsr)==1 &&
      get_V_flag(cpsr)==1) count+=512;
}

void test_ADCS() {
  uint32_t rd, cpsr;
  //the first msr instruction sets the C bit
  asm("msr CPSR_f, #0x20000000\n\t"
      "mov r0,#2\n\t"
      "ADCs %0,r0,#1\n\t"
      "mrs %1,CPSR"
      : "=r" (rd), "=r" (cpsr));
  if (rd==4 &&
      get_N_flag(cpsr)==0 &&
      get_Z_flag(cpsr)==0 &&
      get_C_flag(cpsr)==0 &&
      get_V_flag(cpsr)==0) count+=1024;
}

void test_ORRS() {
  uint32_t two=2, rd, cpsr;
  asm("msr CPSR_f, #0xf0000000\n\t"
      "ORRs %0,%2,#2\n\t"
      "mrs %1,CPSR"
      : "=r" (rd), "=r" (cpsr)
      : "r" (two));
  if (rd==2 &&
      get_N_flag(cpsr)==0 &&
      get_Z_flag(cpsr)==0 &&
      get_C_flag(cpsr)==1 &&
      get_V_flag(cpsr)==1) count+=2048;//update N Z C
}

void test_BICS() {
  uint32_t rd, cpsr;
  asm("mov r0,#1\n\t"
      "BICs %0,r0,#0xfffffff0\n\t"
      "mrs %1,CPSR"
      : "=r" (rd), "=r" (cpsr)
      : 
      : "r0");                                      
  if (rd==1 &&
      get_N_flag(cpsr)==0 &&
      get_Z_flag(cpsr)==0) count+=0x1000;
}

void test_TST() {
  uint32_t cpsr;
  asm("msr CPSR_f, #0x20000000\n\t" // set C bit
      "mov r0, #1\n\t"
      "TST r0, #3\n\t"
      "mrs %0, CPSR"
      : "=r" (cpsr));
  if (get_N_flag(cpsr)==0 &&
      get_Z_flag(cpsr)==0 &&
      get_C_flag(cpsr)==1 &&                          
      get_V_flag(cpsr)==0) count+=0x2000;
}

void test_TEQ() {
  uint32_t cpsr;
  asm("msr CPSR_f, #0x20000000\n\t" // set C bit
      "mov r0, #1\n\t"
      "TEQ r0, #1\n\t"
      "mrs %0, CPSR"
      : "=r" (cpsr));
  if (get_N_flag(cpsr)==0 &&
      get_Z_flag(cpsr)==1 &&
      get_C_flag(cpsr)==1 &&
      get_V_flag(cpsr)==0) count+=0x4000;
}

void test_SBCS() {
  uint32_t rd, cpsr;
  asm("msr CPSR_f, #0x20000000\n\t" // set C bit
      "mov r0, #2\n\t"
      "SBCs %0, r0, #1\n\t"
      "mrs %1, CPSR"
      : "=r" (rd), "=r" (cpsr));
  if (rd==1 &&
      get_N_flag(cpsr)==0 &&
      get_Z_flag(cpsr)==0 &&
      get_C_flag(cpsr)==1 &&
      get_V_flag(cpsr)==0) count+=0x8000;
}

void test_RSCS() {
  uint32_t rd, cpsr;
  asm("msr CPSR_f, #0x20000000\n\t" // set C bit
      "mov r0, #1\n\t"
      "RSCs %0, r0, #2\n\t"
      "mrs %1, CPSR"
      :"=r" (rd), "=r" (cpsr));
  if (rd==1 &&
      get_N_flag(cpsr)==0 &&
      get_Z_flag(cpsr)==0 &&
      get_C_flag(cpsr)==1 &&
      get_V_flag(cpsr)==0) count+=0x10000;
}

void test_CMN() {
  uint32_t cpsr;
  asm("msr CPSR_f, #0x20000000\n\t" // set C bit
      "mov r0, #1\n\t"
      "CMN r0, #1\n\t"
      "mrs %0, CPSR"
      : "=r" (cpsr));
  if (get_N_flag(cpsr)==0 &&
      get_Z_flag(cpsr)==0 &&
      get_C_flag(cpsr)==0 &&
      get_V_flag(cpsr)==0) count+=0x20000;
}

void test_MVNS() {
  uint32_t rd, cpsr;
  asm("msr CPSR_f, #0x20000000\n\t" // set C bit
      "MVNs %0,#0xfffffffe\n\t"
      "mrs %1,CPSR"
      : "=r" (rd), "=r" (cpsr));
  if (rd==1 &&
      get_N_flag(cpsr)==0 &&
      get_Z_flag(cpsr)==0 &&
      get_C_flag(cpsr)==1 &&
      get_V_flag(cpsr)==0) count+=0x40000;
}

int main() {
  test_LSL_shift_imm();
  test_LSR_shift_imm();
  test_ASR_shift_imm();
  test_ROR_shift_imm();
  test_LSL_reg();
  test_LSR_reg();
  test_ASR_reg();
  test_ROR_reg();
  test_RRX();
  test_EORS();
  test_ADCS();
  test_ORRS();
  test_BICS();
  test_TST();
  test_TEQ();
  test_SBCS();
  test_RSCS();
  test_CMN();
  test_MVNS();
  return count;
}
