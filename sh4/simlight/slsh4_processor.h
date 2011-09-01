/* SimSoC-Cert, a library on processor architectures for embedded systems. */
/* See the COPYRIGHTS and LICENSE files. */

/* the main class */

#ifndef SLSH4_PROCESSOR_H
#define SLSH4_PROCESSOR_H

#include "common.h"
#include "sh4_mmu.h"
#include "slsh4_status_register.h"

BEGIN_SIMSOC_NAMESPACE

struct SLSH4_Processor {
  struct SLSH4_MMU *mmu_ptr;
  uint32_t pc;

  /* true if last instruction modified the pc; must be cleared after each step */
  bool jump;

  uint32_t R[24]; // R0_BANK0-R7_BANK0, R0_BANK1-R7_BANK1, R8-R15
  struct SLSH4_StatusRegister SR;
  struct SLSH4_StatusRegister SSR;
  uint32_t SPC;
  uint32_t GBR;
  uint32_t VBR;
  uint32_t SGR;
  uint32_t DBR;
  uint32_t MACH;
  uint32_t MACL;
  uint32_t PR;

  // MMU 
} SLSH4_Processor;

extern void init_processor(struct SLSH4_Processor* , struct SLSH4_MMU*);

extern void destruct_processor(struct SLSH4_Processor*);

extern uint32_t *addr_of_reg_m(struct SLSH4_Processor*, uint8_t reg_id);

static inline uint32_t *addr_of_reg(struct SLSH4_Processor *proc, uint8_t reg_id) {
  return addr_of_reg_m(proc,reg_id);
}

static inline uint32_t reg_m(struct SLSH4_Processor *proc, uint8_t reg_id) {
  return *addr_of_reg_m(proc,reg_id);
}

static inline void set_reg_m(struct SLSH4_Processor *proc, uint8_t reg_id, uint32_t data) {
  *addr_of_reg_m(proc,reg_id) = data;
}

static inline uint32_t reg(struct SLSH4_Processor *proc, uint8_t reg_id) {
  return reg_m(proc,reg_id);
}

static inline uint32_t reg_bank(struct SLSH4_Processor *proc, uint8_t reg_id) {
  return reg_m(proc,reg_id/*,proc->cpsr.mode*/);
}

static inline void set_reg(struct SLSH4_Processor *proc, uint8_t reg_id, uint32_t data) {
  set_reg_m(proc,reg_id, data);
}

static inline void set_reg_bank(struct SLSH4_Processor *proc, uint8_t reg_id, uint32_t data) {
  /* TBD */

  set_reg_m(proc,reg_id, data);
}

static inline uint32_t inst_size(struct SLSH4_Processor *proc) {
  return 2;
}

static inline void set_pc_raw(struct SLSH4_Processor *proc, uint32_t new_pc) {
  assert(!(new_pc&(inst_size(proc)-1)) && "pc misaligned");
  proc->jump = true; proc->pc = new_pc;
}

static inline void set_pc(struct SLSH4_Processor *proc, uint32_t new_pc) {
  set_pc_raw(proc, new_pc & ~1);
}

static inline uint32_t address_of_current_instruction(struct SLSH4_Processor *proc) {
  return proc->pc;
}

END_SIMSOC_NAMESPACE

#endif /* SLSH4_PROCESSOR_H */
