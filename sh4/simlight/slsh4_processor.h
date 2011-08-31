/* SimSoC-Cert, a library on processor architectures for embedded systems. */
/* See the COPYRIGHTS and LICENSE files. */

/* the main class */

#ifndef SLSH4_PROCESSOR_H
#define SLSH4_PROCESSOR_H

#include "common.h"
#include "sh4_mmu.h"

BEGIN_SIMSOC_NAMESPACE

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

extern uint32_t *addr_of_reg_m(struct SLSH4_Processor*, uint8_t reg_id);

static inline uint32_t *addr_of_reg(struct SLSH4_Processor *proc, uint8_t reg_id) {
  return addr_of_reg_m(proc,reg_id);
}

static inline uint32_t reg_m(struct SLSH4_Processor *proc, uint8_t reg_id/*, SLSH4_Mode m*/) {
  return *addr_of_reg_m(proc,reg_id/*,m*/);
}

static inline void set_reg_m(struct SLSH4_Processor *proc, uint8_t reg_id/*, SLSH4_Mode m*/, uint32_t data) {
  *addr_of_reg_m(proc,reg_id/*,m*/) = data;
}

static inline uint32_t reg(struct SLSH4_Processor *proc, uint8_t reg_id) {
  return reg_m(proc,reg_id/*,proc->cpsr.mode*/);
}

static inline uint32_t reg_bank(struct SLSH4_Processor *proc, uint8_t reg_id) {
  return reg_m(proc,reg_id/*,proc->cpsr.mode*/);
}

static inline void set_reg(struct SLSH4_Processor *proc, uint8_t reg_id, uint32_t data) {
  assert(reg_id!=15);
  set_reg_m(proc,reg_id,/*proc->cpsr.mode,*/data);
}

static inline void set_reg_bank(struct SLSH4_Processor *proc, uint8_t reg_id, uint32_t data) {
  assert(reg_id!=15);
  set_reg_m(proc,reg_id,/*proc->cpsr.mode,*/data);
}

static inline uint32_t inst_size(struct SLSH4_Processor *proc) {
  return /*proc->cpsr.T_flag ? 2 : */4; // FIXME
}

static inline void set_pc_raw(struct SLSH4_Processor *proc, uint32_t new_pc) {
  /* never set thumb/arm32 mode */
  assert(!(new_pc&(inst_size(proc)-1)) && "pc misaligned");
  proc->jump = true; *proc->pc = new_pc + 2*inst_size(proc);
}

END_SIMSOC_NAMESPACE

#endif /* SLSH4_PROCESSOR_H */
