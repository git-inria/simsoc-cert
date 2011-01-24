/* Derived from SimSoC, Copyright © INRIA 2007, 2008, 2009, 2010
 * LGPL license version 3 */

/* test thumb v6 new instructions: CPS CPY SETEND
 * After ?? instructions executed, r0 should contain ?? */

#include "common.h"

int count = 0;
int index_ = 1;
#define CHECK(COND)                         \
  if (COND) count += index_; index_ <<= 1;

int A_flag(uint32_t cpsr){return cpsr&(1<<8);}
int I_flag(uint32_t cpsr){return cpsr&(1<<7);}
int F_flag(uint32_t cpsr){return cpsr&(1<<6);}
int E_flag(uint32_t cpsr){return cpsr&(1<<9);}


/* Change Processor State is available only in privileged modes. It changes one or more of the A, I, and F */
/* interrupt disable bits and the mode bits of the CPSR, without changing the other CPSR bits. */
void thumb_CPS(){
  uint32_t  cpsr7,cpsr14;
  asm(
      "cpsid aif\n\t"
      "mrs %0, cpsr\n\t"
      : "=&r" (cpsr7));
  asm("cpsie aif\n\t"
      "mrs %0, cpsr\n\t"
      : "=&r" (cpsr14));
  CHECK((A_flag(cpsr7) == 1)&&(I_flag(cpsr7) == 1)&&(F_flag(cpsr7) == 1));
  CHECK((A_flag(cpsr14) == 0)&&(I_flag(cpsr14) == 0)&&(F_flag(cpsr14) == 0));
}

/* Copy is a pre-UAL synonym for MOV (register). */
/* Move (register) copies a value from a register to the destination register. It can optionally update the */
/* condition flags based on the value. */
void thumb_CPY(){
  uint32_t x1,x2,x3,x4;
    asm("cpy %0, %1\n\t"
	: "=&r" (x1)
	:"r" (0x0));
    asm("cpy %0, %1\n\t"
	: "=&r" (x2)
	:"r" (0xffffffff));
    asm("cpy %0, %1\n\t"
	: "=&r" (x3)
	:"r" (0xffff));
    asm("cpy %0, %1\n\t"
	: "=&r" (x4)
	:"r" (0xffff0000));
    CHECK((x1 == 0x0));
    CHECK((x2 == 0xffffffff));
    CHECK((x3 == 0xffff));
    CHECK((x4 == 0xffff0000));
}

/* Set Endianness writes a new value to ENDIANSTATE. */
void thumb_SETEND_LE(){
  uint32_t f;
    asm("setend le\n\t"
	"mrs %0, cpsr"
	:"=&r" (f));
    CHECK(E_flag(f) == 0);
}
void thumb_SETEND_BE(){
  uint32_t f;
    asm("setend be\n\t"
	"mrs %0, cpsr"
	:"=&r" (f));
    CHECK(E_flag(f) == 1);
}


int main() {
  thumb_CPS();
  thumb_CPY();
  thumb_SETEND_LE();
  thumb_SETEND_BE();
  return count;
}
