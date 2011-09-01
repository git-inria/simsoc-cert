/* SimSoC-Cert, a library on processor architectures for embedded systems. */
/* See the COPYRIGHTS and LICENSE files. */

/* Arithmetic and logic functions. */

#include "slsh4_math.h"

BEGIN_SIMSOC_NAMESPACE

void set_field(uint32_t *dst, uint32_t a, uint32_t b, uint32_t src) {
  assert(a>b);
  if (a-b+1==32) {
    *dst = src;
    return;
  }
  const uint32_t mask = ((1<<(a-b+1))-1)<<b;
  *dst &= ~mask;
  *dst |= (src<<b)&mask;
}

uint32_t Read_Byte(uint32_t n) {
  return n;
}

uint32_t Write_Byte(uint32_t n, uint32_t n2) {
  return n;
}

uint32_t Read_Long(uint32_t n) {
  return n;
}

uint32_t Write_Long(uint32_t n, uint32_t n2) {
  return n;
}

uint32_t Read_Word(uint32_t n) {
  return n;
}

uint32_t Write_Word(uint32_t n, uint32_t n2) {
  return n;
}

void Delay_Slot(struct SLSH4_Processor *proc, uint32_t addr) {
  proc->delayed = true;
  proc->slot_pc = addr;
}

uint32_t succ(uint32_t n) {
  return n + 1;
}

uint32_t pred(uint32_t n) {
  return n - 1;
}

uint32_t bool_of_word(uint32_t n) {
  return n;
}

void if_is_write_back_memory_and_look_up_in_operand_cache_eq_miss_then_allocate_operand_cache_block(uint32_t n) {
  return ;
}

void if_is_dirty_block_then_write_back(uint32_t a) {
  return ;
}

void invalidate_operand_cache_block(uint32_t a) {
  return ;
}

void Sleep_standby(void) {
  return ;
}

END_SIMSOC_NAMESPACE
