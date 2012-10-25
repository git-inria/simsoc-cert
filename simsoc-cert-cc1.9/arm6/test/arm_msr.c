/* Derived from SimSoC, Copyright © INRIA 2007, 2008, 2009, 2010
 * LGPL license version 3 */

/* test the MSR instruction
 * After 639 instructions executed, r0 should contain 0x1ffff */

#include "common.h"

int count = 0;

#define CHECK(ID, COND)                         \
  if (COND) count+=(ID);

typedef enum {N,Z,C,V,F,I,T} flag_t;
const int flag_bit_numbers[7] = {31,30,29,28,6,7,5};

const uint32_t ARM_UND = 0x1b;

void check_flag(uint32_t word, flag_t flag, int expected, int id) {
  const int value = word & (1<<flag_bit_numbers[flag]);
  CHECK(id, !((value && !expected) ||(!value && expected)));
}

void check_mode(uint32_t word, uint32_t expected, int id) {
  CHECK(id, expected==(word & 0x1F));
}


void test() __attribute__ ((noinline));
void test() {
  uint32_t x;
  uint32_t y;
  asm ("mrs %0, CPSR"
       : "=r" (x) );
  check_flag(x,N,1,1);
  check_flag(x,Z,0,2);
  check_flag(x,C,0,4);
  check_flag(x,V,0,8);
  check_flag(x,I,1,16);
  check_flag(x,F,1,32);
  check_flag(x,T,0,64);
  check_mode(x,ARM_UND,128);
  asm volatile ("mov r0,#0xC0000000\n\t"
                "add r0,r0,#0xDB\n\t"
                "msr SPSR_fc,r0\n\t"
                "mrs %0, SPSR\n\t"
                : "=r" (y)
                :
                : "r0");
  check_flag(y,N,1,256);
  check_flag(y,Z,1,512);
  check_flag(y,C,0,1024);
  check_flag(y,V,0,2048);
  check_flag(y,I,1,0x1000);
  check_flag(y,F,1,0x2000);
  check_flag(y,T,0,0x4000);
  check_mode(y,ARM_UND,0x8000);
  return;
}

#define SET_MODE(m)                             \
  asm volatile ("mrs r0, CPSR\n\t"              \
                "bic r0, r0, #0x1f\n\t"         \
                "orr r0, r0, #" #m "\n\t"       \
                "msr CPSR_c, r0")

#define INIT_UND_STACK()                        \
  SET_MODE(0x1B);                               \
  asm volatile ("mov     sp, #0xf000");         \
  SET_MODE(0x1f)

int main () {
  INIT_UND_STACK();
  asm volatile ("msr CPSR_f,#0x80000000\n\t"
                "msr CPSR_c,#0x000000DB"); /* set flags and change to UND mode */
  test();
  asm volatile ("msr CPSR_c,#0x000000DF"); /* return to SYSTEM mode */
  count += 0x10000; /* print_str("End of Test.\n"); */
  return count;
}
