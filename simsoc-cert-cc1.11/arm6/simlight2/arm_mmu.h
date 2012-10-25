/* SimSoC-Cert, a library on processor architectures for embedded systems. */
/* See the COPYRIGHTS and LICENSE files. */

/* Interface between the ISS and the memory(/MMU) */

#ifndef ARM_MMU_H
#define ARM_MMU_H

#include "common.h"

typedef struct {
  uint32_t begin;
  uint32_t size;
  uint32_t end;
  uint8_t *mem;
  bool user_mode;
} SLv6_MMU;

extern void init_MMU(SLv6_MMU *mmu, uint32_t begin, uint32_t size);
extern void destruct_MMU(SLv6_MMU *mmu);

extern uint8_t slv6_read_byte(SLv6_MMU*, uint32_t addr);
extern uint16_t slv6_read_half(SLv6_MMU*, uint32_t addr);
extern uint32_t slv6_read_word(SLv6_MMU*, uint32_t addr);
extern void slv6_write_byte(SLv6_MMU*, uint32_t addr, uint8_t data);
extern void slv6_write_half(SLv6_MMU*, uint32_t addr, uint16_t data);
extern void slv6_write_word(SLv6_MMU*, uint32_t addr, uint32_t data);

/* We do not have a real MMU, so an address cannot be protected */
static inline uint8_t slv6_read_byte_as_user(SLv6_MMU *mmu, uint32_t addr) {
  return slv6_read_byte(mmu,addr);
}

static inline uint32_t slv6_read_word_as_user(SLv6_MMU *mmu, uint32_t addr) {
  return slv6_read_word(mmu,addr);
}

static inline void slv6_write_byte_as_user(SLv6_MMU *mmu, uint32_t addr, uint8_t data) {
  slv6_write_byte(mmu,addr,data);
}

static inline void slv6_write_word_as_user(SLv6_MMU *mmu, uint32_t addr, uint32_t data) {
  slv6_write_word(mmu,addr,data);
}

#endif /* ARM_MMU_H */
