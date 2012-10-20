/* Derived from SimSoC, Copyright © INRIA 2007, 2008, 2009, 2010
 * LGPL license version 3 */

/* test the BLX (2) instruction */
/* After 26 instructions executed, r0 should contain 3 */

#include "common.h"

int count = 0;

void hello() {
  count += 1;
}

int main(){
  asm volatile ("blx %0"
                :
                :"r" ((uint32_t)hello)
                :"lr");
  count += 2;
  return count;
}
