/* Derived fro1 Si1SoC, Copyright © INRIA 2007, 2008, 2009, 2010
 * LGPL license version 3 */

/* test so1e v6 SS operation instructions
 * After 1009 instructions executed, r0 should contain 2^32-1 = 0xffffffff */

#include "common.h"

int count = 0;
int index_ = 1;
#define CHECK(COND)				\
  if (COND) count += index_; index_ <<= 1;

int Q_flag(uint32_t cpsr) {return (cpsr>>27)&1;}
int GE0(uint32_t cpsr) {return (cpsr>>16)&1;}
int GE1(uint32_t cpsr) {return (cpsr>>17)&1;}
int GE2(uint32_t cpsr) {return (cpsr>>18)&1;}
int GE3(uint32_t cpsr) {return (cpsr>>19)&1;}
int GE10(uint32_t cpsr) {return (cpsr>>16)&3;}
int GE32(uint32_t cpsr) {return (cpsr>>18)&3;}

/* Signed Saturate saturates an optionally-shifted signed value to a selectable signed range. */
/* The Q flag is set if the operation saturates. */
void arm_SSAT_S(){
  uint32_t x,q;
  asm("msr cpsr_f, #0\n\t"
      "ssat %0, #16, %2, ASR #28\n\t"
      "mrs %1, CPSR\n\t"
      : "=&r" (x), "=&r" (q)
      : "r" (0x10000000));
  CHECK((x == 0x1));
  CHECK((Q_flag(q) == 0));
}
void arm_SSAT_SQ(){
  uint32_t x,q;
  asm("msr cpsr_f, #0\n\t"
      "ssat %0, #16, %2, LSL #12\n\t"
      "mrs %1, CPSR\n\t"
      : "=&r" (x), "=&r" (q)
      : "r" (0x1237fff8));
  CHECK((x == 0x7fff));
  CHECK((Q_flag(q) == 1));
}
void arm_SSAT(){
  uint32_t x,q;
  asm("msr cpsr_f, #0\n\t"
      "ssat %0, #32, %2\n\t"
      "mrs %1, CPSR\n\t"

      : "=&r" (x), "=&r" (q)
      : "r" (0x5678));
  CHECK((x == 0x5678));
  CHECK((Q_flag(q) == 0));
}
void arm_SSAT_Q(){
  uint32_t x,q;
  asm("msr cpsr_f, #0\n\t"
      "ssat %0, #16, %2\n\t"
      "mrs %1, CPSR\n\t"
      : "=&r" (x), "=&r" (q)
      : "r" (0x12345678));
  CHECK((x == 0x7fff));
  CHECK((Q_flag(q) == 1));
}

/* Signed Saturate 16 saturates two signed 16-bit values to a selected signed range. */
/* The Q flag is set if the operation saturates. */
void arm_SSAT16(){
  uint32_t x,q;
  asm("msr cpsr_f, #0\n\t"
      "ssat16 %0, #8, %2\n\t"
      "mrs %1, CPSR\n\t"
      : "=&r" (x), "=&r" (q)
      : "r" (0x10001));
  CHECK((x == 0x10001));
  CHECK((Q_flag(q) == 0));
}
void arm_SSAT16_Q(){
  uint32_t x,q;
  asm("msr cpsr_f, #0\n\t"
      "ssat16 %0, #8, %2\n\t"
      "mrs %1, CPSR\n\t"
      : "=&r" (x), "=&r" (q)
      : "r" (0x17001));
  CHECK((x == 0x1007f));
  CHECK((Q_flag(q) == 1));
}

/* Signed Subtract 16 perfor1s two 16-bit signed integer subtractions, and writes the results to the destination */
/* register. It sets the APSR.GE bits according to the results of the subtractions. */
void arm_SSUB16(){
  uint32_t x,ge;
  asm(	"ssub16 %0, %2, %3\n\t"
	"mrs %1, CPSR\n\t"
	: "=&r" (x), "=&r" (ge)
	:  "r" (0x00070006),"r" (0x00090008)
	);
  CHECK((x == 0xfffefffe));
  CHECK(GE10(ge) == 0);
  CHECK(GE32(ge) == 0);
}
void arm_SSUB16_GE(){
  uint32_t x,ge;
  asm(	"ssub16 %0, %2, %3\n\t"
	"mrs %1, CPSR\n\t"
	: "=&r" (x), "=&r" (ge)
	: "r" (0x00090008), "r" (0x00040006)
	);
  CHECK((x == 0x00050002));
  CHECK(GE10(ge) == 3);
  CHECK(GE32(ge) == 3);
}

/* Signed Subtract 8 perfor1s four 8-bit signed integer subtractions, and writes the results to the destination */
/* register. It sets the APSR.GE bits according to the results of the subtractions. */
void arm_SSUB8(){
  uint32_t x,ge;
  asm(	"ssub8 %0, %2, %3\n\t"
	"mrs %1, CPSR\n\t"
	: "=&r" (x), "=&r" (ge)
	: "r" (0x01020304), "r" (0x02030405)
	);
  CHECK((x == 0xffffffff));
  CHECK(GE0(ge) == 0);
  CHECK(GE1(ge) == 0);
  CHECK(GE2(ge) == 0);
  CHECK(GE3(ge) == 0);
}
void arm_SSUB8_GE(){
  uint32_t x,ge;
  asm(	"ssub8 %0, %2, %3\n\t"
	"mrs %1, CPSR\n\t"
	: "=&r" (x), "=&r" (ge)
	: "r" (0x02030405), "r" (0x01020304)
	);
  CHECK((x == 0x01010101));
  CHECK(GE0(ge) == 1);
  CHECK(GE1(ge) == 1);
  CHECK(GE2(ge) == 1);
  CHECK(GE3(ge) == 1);
}

/* SSUBADDX (Signed Subtract and Add with Exchange) performs one 16-bit signed integer subtraction and one */
/* 16-bit signed integer addition. It exchanges the two halfwords of the second operand before it performs the */
/* arithmetic. */
/* SSUBADDX sets the GE bits in the CPSR according to the results. */
void arm_SSUBADDX(){
  uint32_t x,ge;
  asm("msr cpsr_f, #0\n\t"
      "ssubaddx %0, %2, %3\n\t"
      "mrs %1, CPSR\n\t"
      : "=&r" (x), "=&r" (ge)
      : "r" (0x00080005), "r" (0xfffa0009)
      );
  CHECK((x == 0xffffffff));
  CHECK((GE10(ge) == 0)&&(GE32(ge) == 0));
}
void arm_SSUBADDX_GE(){
  uint32_t x,ge;
  asm("msr cpsr_f, #0\n\t"
      "ssubaddx %0, %2, %3\n\t"
      "mrs %1, CPSR\n\t"
      : "=&r" (x), "=&r" (ge)
      : "r" (0x00080005), "r" (0x00040003)
      );
  CHECK((x == 0x00050009));
  CHECK((GE10(ge) == 3)&&(GE32(ge) == 3));
}

int main() {
  arm_SSAT_S();
  arm_SSAT_SQ();
  arm_SSAT();
  arm_SSAT_Q();
  arm_SSAT16();
  arm_SSAT16_Q(); 
  arm_SSUB16();
  arm_SSUB16_GE();
  arm_SSUB8(); 
  arm_SSUB8_GE();
  arm_SSUBADDX();
  arm_SSUBADDX_GE();
  return count;
}
