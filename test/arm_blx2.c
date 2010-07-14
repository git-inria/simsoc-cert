/* test the BLX (2) instruction */
/* After 26 instructions executed, r0 should contain 2 */

#include "common.h"

int count = 0;

void hello() {
  ++count;
}

int main(){
  asm volatile ("blx %0"
                :
                :"r" ((uint32_t)hello)
                :"lr");
  ++count;
  return count;
}
