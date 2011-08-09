/* SimSoC-Cert, a library on processor architectures for embedded systems. */
/* See the COPYRIGHTS and LICENSE files. */

/* The main class */

#include "slsh4_processor.h"

BEGIN_SIMSOC_NAMESPACE

void init_Processor(struct SLSH4_Processor *proc, struct SLSH4_MMU *m) {
  proc->mmu_ptr = m;
/*
  set_StatusRegister(&proc->cpsr,0x1df); // = 0b111011111 = A+I+F+System
  struct SLv6_StatusRegister *sr = proc->spsrs, *sr_end = proc->spsrs+5;
  for (; sr!=sr_end; ++sr)
    set_StatusRegister(sr,0x1f);
  init_CP15(&proc->cp15);
  // init registers to 0
  int i = 0;
  for (;i<2;++i)
    proc->user_regs[i] = proc->fiq_regs[i] = proc->irq_regs[i] = proc->svc_regs[i] =
      proc->abt_regs[i] = proc->und_regs[i] = 0;
  for (;i<7;++i)
    proc->user_regs[i] = proc->fiq_regs[i] = 0;
  for (;i<16;++i)
    proc->user_regs[i] = 0;
  proc->pc = &proc->user_regs[15];
  proc->jump = false;
*/
}

void destruct_Processor(struct SLSH4_Processor *proc) {
  destruct_MMU(proc->mmu_ptr);
}

uint32_t *addr_of_reg_m(struct SLSH4_Processor *proc, uint8_t reg_id/*, SLv6_Mode m*/) {
  /*switch (m) {
  case fiq:
    return (8<=reg_id && reg_id<=14) ?
      &proc->fiq_regs[reg_id-8] : &proc->user_regs[reg_id];
  case irq:
    return (13<=reg_id && reg_id<=14) ?
      &proc->irq_regs[reg_id-13] : &proc->user_regs[reg_id];
  case svc:
    return (13<=reg_id && reg_id<=14) ?
      &proc->svc_regs[reg_id-13] : &proc->user_regs[reg_id];
  case abt:
    return (13<=reg_id && reg_id<=14) ?
      &proc->abt_regs[reg_id-13] : &proc->user_regs[reg_id];
  case und:
    return (13<=reg_id && reg_id<=14) ?
      &proc->und_regs[reg_id-13] : &proc->user_regs[reg_id];
  case sys: // no break;
  case usr:
    return &proc->user_regs[reg_id];
    }*/
  abort();
}

END_SIMSOC_NAMESPACE
