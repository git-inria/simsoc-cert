/* SimSoC-Cert, a library on processor architectures for embedded systems. */
/* See the COPYRIGHTS and LICENSE files. */

/* The main class */

#include "slv6_processor.h"

BEGIN_SIMSOC_NAMESPACE

void init_Processor(struct SLv6_Processor *proc,
                    SLv6_MMU *m,
                    SLv6_SystemCoproc *sc) {
  proc->mmu_ptr = m;
  proc->cp15_ptr = sc;
  set_StatusRegister(&proc->cpsr,0x1df); /* = 0b111011111 = A+I+F+System */
  struct SLv6_StatusRegister *sr = proc->spsrs, *sr_end = proc->spsrs+5;
  for (; sr!=sr_end; ++sr)
    set_StatusRegister(sr,0x1f);
  /* init all registers to 0 */
  int i = 0;
  for (;i<2;++i)
    proc->user_regs[i] = proc->fiq_regs[i] = proc->irq_regs[i] = proc->svc_regs[i] =
      proc->abt_regs[i] = proc->und_regs[i] = proc->regs[i] = 0;
  for (;i<7;++i)
    proc->user_regs[i] = proc->fiq_regs[i] = proc->regs[i] = 0;
  for (;i<16;++i)
    proc->regs[i] = 0;
  proc->jump = false;
}

void destruct_Processor(struct SLv6_Processor *proc) {
  destruct_MMU(proc->mmu_ptr);
}

void set_cpsr_mode(struct SLv6_Processor *proc, SLv6_Mode im) {
  int i;
  SLv6_Mode om = proc->cpsr.mode; /* "out" mode */
  if (om==im) return; /* nothing to do */
  proc->cpsr.mode = im; /* "in" mode */
  proc->mmu_ptr->user_mode = im==usr;
  if ((om==usr&&im==sys) || (om==sys&&im==usr)) return; /* nothing more to do */
  if (om==fiq)  /* leave fiq mode */
    for (i = 8; i<13; ++i) {
      proc->fiq_regs[i-8] = proc->regs[i];
      proc->regs[i] = proc->user_regs[i-8];
    }
  if (im==fiq)  /* enter fiq mode */
    for (i = 8; i<13; ++i) {
      proc->user_regs[i-8] = proc->regs[i];
      proc->regs[i] = proc->fiq_regs[i-8];
    }
  switch (om) {
  case fiq:
    proc->fiq_regs[13-8]  = proc->regs[13];
    proc->fiq_regs[14-8]  = proc->regs[14]; break;
  case irq:
    proc->irq_regs[13-13] = proc->regs[13];
    proc->irq_regs[14-13] = proc->regs[14]; break;
  case svc:
    proc->svc_regs[13-13] = proc->regs[13];
    proc->svc_regs[14-13] = proc->regs[14]; break;
  case abt:
    proc->abt_regs[13-13] = proc->regs[13];
    proc->abt_regs[14-13] = proc->regs[14]; break;
  case und:
    proc->und_regs[13-13] = proc->regs[13];
    proc->und_regs[14-13] = proc->regs[14]; break;
  case sys: /* no break; */
  case usr:
    proc->user_regs[13-8] = proc->regs[13];
    proc->user_regs[14-8] = proc->regs[14]; break;
  }
  switch (im) {
  case fiq:
    proc->regs[13] = proc->fiq_regs[13-8];
    proc->regs[14] = proc->fiq_regs[14-8];  break;
  case irq:
    proc->regs[13] = proc->irq_regs[13-13];
    proc->regs[14] = proc->irq_regs[14-13]; break;
  case svc:
    proc->regs[13] = proc->svc_regs[13-13];
    proc->regs[14] = proc->svc_regs[14-13]; break;
  case abt:
    proc->regs[13] = proc->abt_regs[13-13];
    proc->regs[14] = proc->abt_regs[14-13]; break;
  case und:
    proc->regs[13] = proc->und_regs[13-13];
    proc->regs[14] = proc->und_regs[14-13]; break;
  case sys: /* no break; */
  case usr:
    proc->regs[13] = proc->user_regs[13-8];
    proc->regs[14] = proc->user_regs[14-8]; break;
  }
}

uint32_t *addr_of_reg_m(struct SLv6_Processor *proc, uint8_t reg_id, SLv6_Mode m) {
  if (reg_id==15 || reg_id<8 || m==proc->cpsr.mode)
    return &proc->regs[reg_id];
  if (reg_id<13) {
    if (m==fiq) return &proc->fiq_regs[reg_id-8];
    if (proc->cpsr.mode==fiq) return &proc->user_regs[reg_id-8];
    return &proc->regs[reg_id];
  }
  assert((reg_id==13 || reg_id==14) && m!=proc->cpsr.mode);
  switch (m) {
  case fiq: return &proc->fiq_regs[reg_id-8];
  case irq: return &proc->irq_regs[reg_id-13];
  case svc: return &proc->svc_regs[reg_id-13];
  case abt: return &proc->abt_regs[reg_id-13];
  case und: return &proc->und_regs[reg_id-13];
  case sys:
    if (proc->cpsr.mode==usr) return &proc->regs[reg_id];
    else return &proc->user_regs[reg_id-8];
  case usr:
    if (proc->cpsr.mode==sys) return &proc->regs[reg_id];
    else return &proc->user_regs[reg_id-8];
  }
  abort();
}

void slv6_print_reg(FILE *f, uint8_t n) {
  assert(n<16);
  switch (n) {
  case 15: fprintf(f,"PC"); return;
  case 14: fprintf(f,"LR"); return;
  case 13: fprintf(f,"SP"); return;
  default: fprintf(f,"R%d",(int)n);
  }
}

void slv6_print_reglist(FILE *f, uint16_t regs) {
  bool first = true;
  int i;
  fputc('{',f);
  for (i = 0; i<16; ++i)
    if ((regs>>i)&1) {
      if (first) first = false;
      else fprintf(f,", ");
      slv6_print_reg(f,i);
    }
  assert(!first);
  fputc('}',f);
}

END_SIMSOC_NAMESPACE
