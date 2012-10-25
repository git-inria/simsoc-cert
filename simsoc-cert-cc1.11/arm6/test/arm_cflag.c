/* Derived from SimSoC, Copyright © INRIA 2007, 2008, 2009, 2010
 * LGPL license version 3 */

/* test the C flag
 * After 100 instructions executed, r0 should contain 15 */

#include "common.h"

int count = 0;

void test_adc() {
  uint32_t cpsr, result;
  asm("msr CPSR_f,#0x20000000\n\t" /* set C flag */
      "adcs %0,%2,%3\n\t"
      "mrs %1, CPSR"
      : "=r"(result), "=r"(cpsr)
      : "r"(0xcafe), "r"(~0));
  if (result==0xcafe) count+=1;
  if (get_C_flag(cpsr)==1) count+=2;
}

void test_sbc() {
  uint32_t cpsr, result;
  asm("msr CPSR_f,#0x00000000\n\t" /* clear C flag */
      "sbcs %0,%2,%3\n\t"
      "mrs %1, CPSR"
      : "=r"(result), "=r"(cpsr)
      : "r"(0xcafe), "r"(0xcafe));
  if (result==~0) count+=4;
  if (get_C_flag(cpsr)==0) count+=8;
}

int main() {
  test_adc();
  test_sbc();
  return count;
}
