/* SimSoC-Cert, a library on processor architectures for embedded systems. */
/* See the COPYRIGHTS and LICENSE files. */

#include "arm_not_implemented.h"

void dependent_operation(struct SLv6_Processor *proc, uint8_t n) {
  if (n==15) dependent_operation_CP15(&proc->cp15);
  else TODO("undefined instruction");
}

void load(struct SLv6_Processor *proc, uint8_t n, uint32_t x) {
  if (n==15) load_CP15(&proc->cp15,x);
  else TODO("undefined instruction");
}

void send(struct SLv6_Processor *proc, uint8_t n, uint32_t x) {
  if (n==15) send_CP15(&proc->cp15,x);
  else TODO("undefined instruction");
}

bool NotFinished(struct SLv6_Processor *proc, uint8_t n) {
  if (n==15) return NotFinished_CP15(&proc->cp15);
  else TODO("undefined instruction");
}

uint32_t first_value(struct SLv6_Processor *proc, uint8_t n) {
  if (n==15) return first_value_CP15(&proc->cp15);
  else TODO("undefined instruction");
}

uint32_t second_value(struct SLv6_Processor *proc, uint8_t n) {
  if (n==15) return second_value_CP15(&proc->cp15);
  else TODO("undefined instruction");
}

uint32_t value(struct SLv6_Processor *proc, uint8_t n) {
  if (n==15) return value_CP15(&proc->cp15);
  else TODO("undefined instruction");
}
