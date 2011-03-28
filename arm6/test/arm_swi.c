/* Derived from SimSoC, Copyright © INRIA 2007, 2008, 2009, 2010
 * LGPL license version 3 */

/* test the SWI instruction
 * After 45 instructions executed, r0 should contain 3 */

#include "common.h"

int count = 0;

void handler() __attribute__ ((interrupt("SWI")));
void handler() {
  count+=1;
}

#define SET_MODE(m)                                       \
  asm volatile ("mrs r0, CPSR\n\t"                        \
                "bic r0, r0, #0x1f\n\t"                   \
                "orr r0, r0, #" #m "\n\t"                 \
                "msr CPSR_c, r0": : :"r0")

#define SET_SWI_HANDLER(f)                                              \
  *((volatile uint32_t *) (0x8+8+0x10)) = (uint32_t) f;                \
  *((volatile uint32_t *) 0x8) = 0xe59ff010 // ldr pc, [pc, #+16]

#define INIT_SWI_STACK()                           \
  SET_MODE(0x13);                                  \
  asm ("mov     sp, #0xf000");                     \
  SET_MODE(0x1f)

int main()
{
  SET_SWI_HANDLER(handler);
  INIT_SWI_STACK();
  asm ("swi     #42");
  count+=2; /* print_str(" OK\n"); */
  return count;
}
