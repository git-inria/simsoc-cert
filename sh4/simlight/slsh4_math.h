/* SimSoC-Cert, a library on processor architectures for embedded systems. */
/* See the COPYRIGHTS and LICENSE files. */

/* Arithmetic and logic functions. */

#ifndef SH4_MATH_H
#define SH4_MATH_H

#include "slsh4_processor.h"
#include "common.h"

BEGIN_SIMSOC_NAMESPACE

static inline uint32_t get_bits(uint32_t x, size_t a, size_t b) {
  /* return x[a:b] */
  assert(32>a && a>b && a-b+1 < 32);
  return (x>>b) & ((1lu<<(a-b+1))-1);
}

extern void set_field(uint32_t *dst, uint32_t a, uint32_t b, uint32_t src);
/* dst[a:b] = src, with a>b */

extern uint8_t Read_Byte(struct SLSH4_Processor *proc, uint32_t Addr);
extern uint16_t Read_Word(struct SLSH4_Processor *proc, uint32_t Addr);
extern uint32_t Read_Long(struct SLSH4_Processor *proc, uint32_t Addr);
extern uint8_t Write_Byte(struct SLSH4_Processor *proc, uint32_t Addr, uint32_t Data);
extern uint16_t Write_Word(struct SLSH4_Processor *proc, uint32_t Addr, uint32_t Data);
extern uint32_t Write_Long(struct SLSH4_Processor *proc, uint32_t Addr, uint32_t Data);
extern void Delay_Slot(struct SLSH4_Processor *proc, uint32_t addr);
extern uint32_t succ(uint32_t a);
extern uint32_t pred(uint32_t a);
extern uint32_t bool_of_word(uint32_t a);
extern void if_is_write_back_memory_and_look_up_in_operand_cache_eq_miss_then_allocate_operand_cache_block(uint32_t a);
extern void if_is_dirty_block_then_write_back(uint32_t a);
extern void invalidate_operand_cache_block(uint32_t a);
extern void Sleep_standby(void);

END_SIMSOC_NAMESPACE

#endif /* SH4_MATH_H */
