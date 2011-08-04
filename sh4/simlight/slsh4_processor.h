/* SimSoC-Cert, a library on processor architectures for embedded systems. */
/* See the COPYRIGHTS and LICENSE files. */

/* the main class */

#ifndef SLSH4_PROCESSOR_H
#define SLSH4_PROCESSOR_H

#include "common.h"
#include "sh4_mmu.h"

struct SLSH4_Processor {
  struct SLSH4_MMU *mmu_ptr;

  uint32_t *pc; /* = &user_regs[15] */

  /* true if last instruction modified the pc; must be cleared after each step */
  bool jump;

  // registers
    // Sixteen 32-bit general registers (and eight 32-bit shadow registers)
    // Seven 32-bit control registers
    // Four 32-bit system registers

  // MMU 
} SLSH4_Processor;

extern void init_processor(struct SLSH4_Processor* , struct SLSH4_MMU*);

extern void destruct_processor(struct SLSH4_Processor*);

#endif /* SLSH4_PROCESSOR_H */
