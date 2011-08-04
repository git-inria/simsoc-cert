/* SimSoC-Cert, a library on processor architectures for embedded systems. */
/* See the COPYRIGHTS and LICENSE files. */

/* Interface between the ISS and the memory(/MMU) */

#ifndef SH4_MMU_H
#define SH4_MMU_H

#include "common.h"

struct SLSH4_MMU {
  uint32_t begin;
  uint32_t size;
  uint32_t end;
  uint8_t *mem;
};

extern void init_MMU(struct SLSH4_MMU *mmu, uint32_t begin, uint32_t size);
extern void destruct_MMU(struct SLSH4_MMU *mmu);

extern uint8_t read_byte(struct SLSH4_MMU*, uint32_t addr);
extern uint16_t read_half(struct SLSH4_MMU*, uint32_t addr);
extern uint32_t read_word(struct SLSH4_MMU*, uint32_t addr);
extern void write_byte(struct SLSH4_MMU*, uint32_t addr, uint8_t data);
extern void write_half(struct SLSH4_MMU*, uint32_t addr, uint16_t data);
extern void write_word(struct SLSH4_MMU*, uint32_t addr, uint32_t data);

#endif /* SH4_MMU_H */
