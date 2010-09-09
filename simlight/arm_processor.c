/* SimSoC-Cert, a library on processor architectures for embedded systems. */
/* See the COPYRIGHTS and LICENSE files. */

/* The main class */

#include "arm_processor.h"

void init_Processor(struct Processor *proc) {
  init_MMU(&proc->mmu,4,0x100000);
  set_StatusRegister(&proc->cpsr,0x1df); /* = 0b111011111 = A+I+F+System */
  struct StatusRegister *sr = proc->spsrs, *sr_end = proc->spsrs+5;
  for (; sr!=sr_end; ++sr)
    set_StatusRegister(sr,0x1f);
  init_CP15(&proc->cp15);
  /* init registers to 0 */
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
}

void destruct_Processor(struct Processor *proc) {
  destruct_MMU(&proc->mmu);
}

uint32_t *addr_of_reg_m(struct Processor *proc, uint8_t reg_id, Mode m) {
  switch (m) {
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
  case sys: /* no break; */
  case usr:
    return &proc->user_regs[reg_id];
  }
  abort();
}

void dependent_operation(struct Processor *proc, uint8_t n) {
  if (n==15) dependent_operation_CP15(&proc->cp15);
  else TODO("undefined instruction");
}

void load(struct Processor *proc, uint8_t n, uint32_t x) {
  if (n==15) load_CP15(&proc->cp15,x);
  else TODO("undefined instruction");
}

void send(struct Processor *proc, uint8_t n, uint32_t x) {
  if (n==15) send_CP15(&proc->cp15,x);
  else TODO("undefined instruction");
}

bool NotFinished(struct Processor *proc, uint8_t n) {
  if (n==15) return NotFinished_CP15(&proc->cp15);
  else TODO("undefined instruction");
}

uint32_t first_value(struct Processor *proc, uint8_t n) {
  if (n==15) return first_value_CP15(&proc->cp15);
  else TODO("undefined instruction");
}

uint32_t second_value(struct Processor *proc, uint8_t n) {
  if (n==15) return second_value_CP15(&proc->cp15);
  else TODO("undefined instruction");
}

uint32_t value(struct Processor *proc, uint8_t n) {
  if (n==15) return value_CP15(&proc->cp15);
  else TODO("undefined instruction");
}
