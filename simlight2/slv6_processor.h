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
#include "arm_not_implemented.h"

BEGIN_SIMSOC_NAMESPACE

struct ARMv6_Processor; /* used only in SimSoC */

struct SLv6_Processor {
  SLv6_MMU *mmu_ptr;
  SLv6_SystemCoproc *cp15_ptr;
  struct ARMv6_Processor *proc_ptr; /* used only in SimSoC */
  struct SLv6_StatusRegister cpsr;
  struct SLv6_StatusRegister spsrs[5];
  size_t id;
  uint32_t regs[16];

  /* banked registers */
  uint32_t user_regs[7]; /* 8-14 */
  uint32_t fiq_regs[7]; /*  8-14 */
  uint32_t irq_regs[2]; /* 13-14 */
  uint32_t svc_regs[2]; /* 13-14 */
  uint32_t abt_regs[2]; /* 13-14 */
  uint32_t und_regs[2]; /* 13-14 */

  /* true if last instruction modified the pc; must be cleared after each step */
  bool jump;
};

extern void init_Processor(struct SLv6_Processor*,
                           SLv6_MMU*,
                           SLv6_SystemCoproc*);

extern void destruct_Processor(struct SLv6_Processor*);

extern void set_cpsr_mode(struct SLv6_Processor*, SLv6_Mode m);

static inline void set_cpsr_sr(struct SLv6_Processor *proc,
                               struct SLv6_StatusRegister sr) {
  set_cpsr_mode(proc,sr.mode);
  proc->cpsr = sr;
  update_pending_flags(proc);
}

static inline void set_cpsr_bin(struct SLv6_Processor *proc,
                                uint32_t bin) {
  struct SLv6_StatusRegister sr;
  set_StatusRegister(&sr, bin);
  set_cpsr_mode(proc, sr.mode);
  proc->cpsr = sr;
  update_pending_flags(proc);
}

static inline void set_cpsr_F_flag(struct SLv6_Processor *proc, bool f) {
  proc->cpsr.F_flag = f;
  update_pending_flags(proc);
}

static inline void set_cpsr_I_flag(struct SLv6_Processor *proc, bool i) {
  proc->cpsr.I_flag = i;
  update_pending_flags(proc);
}

static inline void set_cpsr_A_flag(struct SLv6_Processor *proc, bool a) {
  proc->cpsr.A_flag = a;
  update_pending_flags(proc);
}

extern uint32_t *addr_of_reg_m(struct SLv6_Processor*, uint8_t reg_id, SLv6_Mode);

static inline uint32_t reg_m(struct SLv6_Processor *proc,
                             uint8_t reg_id, SLv6_Mode m) {
  return *addr_of_reg_m(proc,reg_id,m);
}

static inline void set_reg_m(struct SLv6_Processor *proc,
                             uint8_t reg_id, SLv6_Mode m, uint32_t data) {
  *addr_of_reg_m(proc,reg_id,m) = data;
}

static inline uint32_t *addr_of_reg(struct SLv6_Processor *proc, uint8_t reg_id) {
  return &proc->regs[reg_id];
}

static inline uint32_t reg(struct SLv6_Processor *proc, uint8_t reg_id) {
  return proc->regs[reg_id];
}

static inline void set_reg(struct SLv6_Processor *proc,
                           uint8_t reg_id, uint32_t data) {
  assert(reg_id!=15);
  proc->regs[reg_id] = data;
}

static inline uint32_t inst_size(struct SLv6_Processor *proc) {
  return proc->cpsr.T_flag ? 2 : 4;
}

static inline void set_pc_raw(struct SLv6_Processor *proc, uint32_t new_pc) {
  /* never set thumb/arm32 mode */
  assert(!(new_pc&(inst_size(proc)-1)) && "pc misaligned");
  proc->jump = true; proc->regs[15] = new_pc + 2*inst_size(proc);
}

static inline void set_reg_or_pc(struct SLv6_Processor *proc,
                                 uint8_t reg_id, uint32_t data) {
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

static inline bool InAPrivilegedMode(struct SLv6_Processor *proc) {
  return proc->cpsr.mode!=usr;
}

static inline bool CurrentModeHasSPSR(struct SLv6_Processor *proc) {
  return proc->cpsr.mode<sys;
}

static inline struct SLv6_StatusRegister *spsr_m(struct SLv6_Processor *proc,
                                                 SLv6_Mode m) {
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
  return proc->regs[15] - inst_size(proc);
}

static inline uint32_t address_of_current_instruction(struct SLv6_Processor *proc) {
  return proc->regs[15] - 2*inst_size(proc);
}

static inline bool high_vectors_configured(const struct SLv6_Processor *proc) {
  return CP15_reg1_Vbit(proc->cp15_ptr);
}

static inline void increment_pc(struct SLv6_Processor *proc) {
  proc->regs[15] += inst_size(proc);
}

static inline void decrement_pc(struct SLv6_Processor *proc) {
  proc->regs[15] -= inst_size(proc);
}

static inline void increment_pc_arm32(struct SLv6_Processor *proc) {
  assert(inst_size(proc)==4);
  proc->regs[15] += 4;
}

static inline void decrement_pc_arm32(struct SLv6_Processor *proc) {
  assert(inst_size(proc)==4);
  proc->regs[15] -= 4;
}

static inline void increment_pc_arm16(struct SLv6_Processor *proc) {
  assert(inst_size(proc)==2);
  proc->regs[15] += 2;
}

static inline void decrement_pc_arm16(struct SLv6_Processor *proc) {
  assert(inst_size(proc)==2);
  proc->regs[15] -= 2;
}

static inline uint32_t get_pc(const struct SLv6_Processor *proc) {
  return proc->regs[15];
}

static inline void slv6_hook(struct SLv6_Processor *proc) {
  /* std::cout <<hex <<"DBG"; */
  /* std::cout <<" R0 = " <<proc->regs[0] <<";"; */
  /* std::cout <<" R1 = " <<proc->regs[1] <<";"; */
  /* std::cout <<" R2 = " <<proc->regs[2] <<";"; */
  /* std::cout <<" R3 = " <<proc->regs[3] <<"\nDBG"; */
  /* std::cout <<" R4 = " <<proc->regs[4] <<";"; */
  /* std::cout <<" R5 = " <<proc->regs[5] <<";"; */
  /* std::cout <<" R6 = " <<proc->regs[6] <<";"; */
  /* std::cout <<" R7 = " <<proc->regs[7] <<"\nDBG"; */
  /* std::cout <<" R8 = " <<proc->regs[8] <<";"; */
  /* std::cout <<" R9 = " <<proc->regs[9] <<";"; */
  /* std::cout <<" R10 = " <<proc->regs[10] <<";"; */
  /* std::cout <<" R11 = " <<proc->regs[11] <<"\nDBG"; */
  /* std::cout <<" R12 = " <<proc->regs[12] <<";"; */
  /* std::cout <<" SP = " <<proc->regs[13] <<";"; */
  /* std::cout <<" LR = " <<proc->regs[14] <<";"; */
  /* std::cout <<" PC = " <<proc->regs[15]-(proc->cpsr.T_flag ? 4 : 8) <<std::endl; */
}

END_SIMSOC_NAMESPACE

#endif /* SLV6_PROCESSOR_H */
