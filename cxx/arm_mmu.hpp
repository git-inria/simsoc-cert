// SimSoC-Cert, a library on processor architectures for embedded systems.
// See the COPYRIGHTS and LICENSE files.

// Interface between the ISS and the memory(/MMU)

#ifndef ARM_MMU_H
#define ARM_MMU_H

#include "common.hpp"

struct MMU {
  uint32_t begin;
  uint32_t size;
  uint32_t end;
  uint8_t *mem;
};

extern void init_MMU(MMU *mmu, uint32_t begin, uint32_t size);
extern void destruct_MMU(MMU *mmu);

extern uint8_t read_byte(MMU*, uint32_t addr);
extern uint16_t read_half(MMU*, uint32_t addr);
extern uint32_t read_word(MMU*, uint32_t addr);
extern void write_byte(MMU*, uint32_t addr, uint8_t data);
extern void write_half(MMU*, uint32_t addr, uint16_t data);
extern void write_word(MMU*, uint32_t addr, uint32_t data);

#endif //ARM_MMU_H
