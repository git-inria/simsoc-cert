/* Derived from SimSoC, Copyright © INRIA 2007, 2008, 2009, 2010
 * LGPL license version 3 */

/* test the LSM instructions
 * After 115 instructions executed, r0 should contain 0x7 */

#include "common.h"

int count = 0;

#define CHECK(ID, RESULT, EXPECTED)             \
  if ((RESULT)==(EXPECTED)) count+=(ID);

#define SET_MODE(m)                                       \
  asm volatile ("mrs r0, CPSR\n\t"                        \
                "bic r0, r0, #0x1f\n\t"                   \
                "orr r0, r0, #" #m "\n\t"                 \
                "msr CPSR_c, r0");

uint32_t stm2 = 0xBAD;

void test_stm_2() {
  uint32_t r14; // = lr
  // read r14_usr
  asm("mov %0, r14": "=r"(r14));
  // go to supervisor mode
  SET_MODE(0x13);
  // put a bad value inside r14_svc
  asm("mov r14,#0x44");
  // store the content of r14_usr in stm2
  asm("stmda %0,{r14}^"
      :
      :"r" (&stm2));
  // return to system mode
  SET_MODE(0x1f);
  // check if the right register has been read
  CHECK(1,stm2,r14);
}

uint32_t ldm2 = 0xBEE;

void test_ldm_2() {
  uint32_t lr_init = 0x44, lr_bee = 0x444;
  // read r14_usr
  asm volatile ("mov %0, r14": "=r"(lr_init));
  // go to supervisor mode
  SET_MODE(0x13);
  // overwrite r14_usr with 0xBEE
  asm volatile ("ldmda %0, {r14}^"
      : // no outputs
      : "r" (&ldm2));
  // return to system mode
  SET_MODE(0x1f);
  // read lr again
  asm volatile ("mov %0, r14": "=r"(lr_bee));
  // check if r14_usr has been written
  CHECK(2,lr_bee,ldm2);
  // restore lr_init, else we cannot return
  asm volatile ("mov r14, %0"
                : // no outputs
                : "r" (lr_init));
}

const int *ldm3_id = NULL;
const int ID = 4;

void set_ldm3_id() {
  ldm3_id = &ID;
}

void test_ldm_3() {
  uint32_t p = (uint32_t) set_ldm3_id;
  asm volatile ("mov r1, %0\n\t"
                "add lr,pc,#16\n\t"
                "mrs r0,CPSR\n\t"
                "bic r0,r0,#0x1f\n\t"
                "orr r0,r0,#0x13\n\t"
                "msr CPSR_c,r0\n\t"
                "ldmda r1!,{r15}^"
                :
                :"r" ((uint32_t)&p), "m" (p) // pc = MEM[&p] = p = set_ldm3_str
                :"lr","r0","r1");
  if (ldm3_id) count += *ldm3_id; // LDM_3 test
}

int main() {
  test_stm_2();
  test_ldm_2();
  test_ldm_3();
  return count;
}
