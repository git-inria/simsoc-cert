/* SimSoC-Cert, a library on processor architectures for embedded systems. */
/* See the COPYRIGHTS and LICENSE files. */

/* The main class */

#ifndef SLV6_PROCESSOR_H
#define SLV6_PROCESSOR_H

#include "common.h"
#include "arm_mmu.h"
#include "slv6_mode.h"
#include "slv6_status_register.h"
#include "arm_system_coproc.h"

BEGIN_SIMSOC_NAMESPACE

struct SLv6_Processor {
  struct SLv6_MMU *mmu_ptr;
  struct SLv6_StatusRegister cpsr;
  struct SLv6_StatusRegister spsrs[5];
  struct SLv6_SystemCoproc cp15;
  size_t id;
  uint32_t user_regs[16];
  uint32_t fiq_regs[7];
  uint32_t irq_regs[2];
  uint32_t svc_regs[2];
  uint32_t abt_regs[2];
  uint32_t und_regs[2];
  uint32_t *pc; /* = &user_regs[15] */

  /* true if last instruction modified the pc; must be cleared after each step */
  bool jump;
};

extern void init_Processor(struct SLv6_Processor*, struct SLv6_MMU*);

extern void destruct_Processor(struct SLv6_Processor*);

extern uint32_t *addr_of_reg_m(struct SLv6_Processor*, uint8_t reg_id, SLv6_Mode);

static inline uint32_t reg_m(struct SLv6_Processor *proc, uint8_t reg_id, SLv6_Mode m) {
  return *addr_of_reg_m(proc,reg_id,m);
}

static inline void set_reg_m(struct SLv6_Processor *proc, uint8_t reg_id, SLv6_Mode m, uint32_t data) {
  *addr_of_reg_m(proc,reg_id,m) = data;
}

static inline uint32_t *addr_of_reg(struct SLv6_Processor *proc, uint8_t reg_id) {
  return addr_of_reg_m(proc,reg_id,proc->cpsr.mode);
}

static inline uint32_t reg(struct SLv6_Processor *proc, uint8_t reg_id) {
  return reg_m(proc,reg_id,proc->cpsr.mode);
}

static inline void set_reg(struct SLv6_Processor *proc, uint8_t reg_id, uint32_t data) {
  assert(reg_id!=15);
  return set_reg_m(proc,reg_id,proc->cpsr.mode,data);
}

static inline uint32_t inst_size(struct SLv6_Processor *proc) {
  return proc->cpsr.T_flag ? 2 : 4;
}

static inline void set_pc_raw(struct SLv6_Processor *proc, uint32_t new_pc) {
  /* never set thumb/arm32 mode */
  assert(!(new_pc&(inst_size(proc)-1)) && "pc misaligned");
  proc->jump = true; *proc->pc = new_pc + 2*inst_size(proc);
}

static inline void set_reg_or_pc(struct SLv6_Processor *proc, uint8_t reg_id, uint32_t data) {
  if (reg_id==15)
    set_pc_raw(proc,data);
  else
    set_reg(proc,reg_id,data);
}


static inline void set_pc(struct SLv6_Processor *proc, uint32_t new_pc) {
  /* may set thumb/arm32 mode */
  proc->cpsr.T_flag = new_pc&1;
  set_pc_raw(proc, new_pc&~1);
}

static inline bool InAPrivilegedMode(struct SLv6_Processor *proc) {return proc->cpsr.mode!=usr;}
static inline bool CurrentModeHasSPSR(struct SLv6_Processor *proc) {return proc->cpsr.mode<sys;}

static inline struct SLv6_StatusRegister *spsr_m(struct SLv6_Processor *proc, SLv6_Mode m) {
  if (m<sys) return &proc->spsrs[m];
  else ERROR("This mode does not have a SPSR");
  abort(); // unreachable
}

static inline struct SLv6_StatusRegister *spsr(struct SLv6_Processor *proc) {
  if (CurrentModeHasSPSR(proc)) return &proc->spsrs[proc->cpsr.mode];
  else ERROR("Current mode does not have a SPSR");
  abort(); // unreachable
}

static inline uint32_t address_of_next_instruction(struct SLv6_Processor *proc) {
  return *proc->pc - inst_size(proc);
}

static inline uint32_t address_of_current_instruction(struct SLv6_Processor *proc) {
  return *proc->pc - 2*inst_size(proc);
}

static inline bool high_vectors_configured(struct SLv6_Processor *proc) {
  return CP15_reg1_Vbit(&proc->cp15);
}

END_SIMSOC_NAMESPACE

#endif /* SLV6_PROCESSOR_H */
