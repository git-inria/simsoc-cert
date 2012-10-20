/* Derived from SimSoC, Copyright © INRIA 2007, 2008, 2009, 2010
 * LGPL license version 3 */

/* test the MRS instruction and software interrupts
 * After 727 instructions executed, r0 should contain 0x7ffff */

#include "common.h"

int count = 0;

#define CHECK(ID, COND)                         \
  if (COND) count+=(ID);

const uint32_t ARM_SVC = 0x13;
const uint32_t ARM_SYSTEM = 0x1f;

void check_flag(uint32_t word, int bit_number, int expected, int id) {
  CHECK(id, !( ((word & (1<<bit_number)) && !expected)
               ||(!(word & (1<<bit_number)) && expected) ));
}

void check_mode(uint32_t word, uint32_t expected, int id) {
  CHECK(id, expected==(word & 0x1F));
}

void handler() __attribute__ ((interrupt("SWI")));
void handler() {
  uint32_t x;
  uint32_t y;
  asm volatile ("movs r0, #1"); /* set N=0 and Z=0 */
  asm volatile ("mrs %0, CPSR"
                : "=r" (x) );
  /* print_str("Value of CPSR inside the SWI handler\n"); */
  check_flag(x,31/*N*/,0,1);
  check_flag(x,30/*Z*/,0,2);
  check_flag(x,7/*I*/,1,4);
  check_flag(x,6/*F*/,1,8);
  check_flag(x,5/*T*/,0,16);
  check_mode(x,ARM_SVC,32);
  asm("mrs %0, SPSR"
       : "=r" (y) );
  /* print_str("Value of SPSR inside the SWI handler\n"); */
  check_flag(y,31/*N*/,0,64);
  check_flag(y,30/*Z*/,1,128);
  check_flag(y,7/*I*/,1,256);
  check_flag(y,6/*F*/,1,512);
  check_flag(y,5/*T*/,0,1024);
  check_mode(y,ARM_SYSTEM,2048);
}

#define SET_MODE(m)                                       \
  asm volatile ("mrs r0, CPSR\n\t"                        \
                "bic r0, r0, #0x1f\n\t"                   \
                "orr r0, r0, #" #m "\n\t"                 \
                "msr CPSR_c, r0")

#define SET_SWI_HANDLER(f)                                              \
  *((volatile uint32_t *) (0x8+8+0x10)) = (uint32_t) f;                \
  *((volatile uint32_t *) 0x8) = 0xe59ff010 // ldr pc, [pc, #+16]

#define INIT_SWI_STACK()                           \
  SET_MODE(0x13);                                  \
  asm volatile ("mov     sp, #0xf000");                     \
  SET_MODE(0x1f)

int main () {
  SET_SWI_HANDLER(handler);
  INIT_SWI_STACK();
  uint32_t x;
  asm volatile ("movs r0, #-1"); /* set N=1 and Z=0 */
  asm volatile ("mrs %0, CPSR"
                : "=r" (x) );
  /* print_str("Value of CPSR inside the main function\n"); */
  check_flag(x,31/*N*/,1,0x1000);
  check_flag(x,30/*Z*/,0,0x2000);
  check_flag(x,7/*I*/,1,0x4000);
  check_flag(x,6/*F*/,1,0x8000);
  check_flag(x,5/*T*/,0,0x10000);
  check_mode(x,ARM_SYSTEM,0x20000);
  asm volatile ("movs r0, #0"); /* set N=0 and Z=1 */
  asm volatile ("swi     #42");
  count += 0x40000; /* print_str("End of Test.\n"); */
  return count;
}
