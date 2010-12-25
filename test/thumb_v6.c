/* Derived from SimSoC, Copyright © INRIA 2007, 2008, 2009, 2010
 * LGPL license version 3 */

/* test some v6 new instructions
 * After ?? instructions executed, r0 should contain ?? */

#include "common.h"

int count = 0;

#define CHECK(ID, COND)                         \
  if (COND) count+=(ID)

/* REMOVE: not an ARMv6 thumb instruction */
/* void thumb_ADD6() { */
/*   uint32_t x,y,z; */
/*   y = 0x4; */
/*   asm("add %0,pc,%1\n\t" */
/*       "mov %2, pc"  */
/*       : "=r" (x), "+&r" (y), "=r" (z)); */
      
/*   CHECK(1, ((z+2)&~2)-2 == (x-4+2)); */
/* } */

/* void thumb_ADR() { */
/*   uint32_t x,y; */
/*   asm("adr %0, #0\n\t" */
/*       "mov %1, pc" */
/*       : "=r" (x), "=&r" (y)); */
/*   CHECK(2, (x == y)); */
/* } */

int main() {
  /* thumb_ADD6(); */
  /* thumb_ADR(); */
  return count;
}
