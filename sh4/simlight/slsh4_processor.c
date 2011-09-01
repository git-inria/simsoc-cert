/* SimSoC-Cert, a library on processor architectures for embedded systems. */
/* See the COPYRIGHTS and LICENSE files. */

/* The main class */

#include "slsh4_processor.h"

BEGIN_SIMSOC_NAMESPACE

void init_Processor(struct SLSH4_Processor *proc, struct SLSH4_MMU *m) {
  proc->mmu_ptr = m;
  proc->pc = malloc(sizeof(uint32_t));
  proc->jump = false;
  proc->VBR = 0x00000000;

  proc->SR.MD = 1;
  proc->SR.RB = 1;
  proc->SR.BL = 1;
  proc->SR.FD = 0;
  proc->SR.IMASK = 0xf;
}

void destruct_Processor(struct SLSH4_Processor *proc) {
  destruct_MMU(proc->mmu_ptr);
}

uint32_t *addr_of_reg_m(struct SLSH4_Processor *proc, uint8_t reg_id) {
  if (proc->SR.MD == 0) {
    if (reg_id < 8)
      return proc->R + reg_id;
    else
      return proc->R + reg_id + 8;
  }
  else {
    if (reg_id < 8) {
      if (proc->SR.RB == 0)
        return proc->R + reg_id;
      else
        return proc->R + reg_id + 8;
    }
    else
      return proc->R + reg_id + 8;
  }

  abort();
}

END_SIMSOC_NAMESPACE
