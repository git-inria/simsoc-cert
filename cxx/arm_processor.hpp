// SimSoC-Cert, a library on processor architectures for embedded systems.
// See the COPYRIGHTS and LICENSE files.

// The main class

#include "common.h"
#include "arm_mmu.h"
#include "arm_mode.h"
#include "arm_status_register.h"
#include "arm_system_coproc.h"
#include <assert.h>

struct Processor {
  MMU mmu;
  StatusRegister cpsr;
  StatusRegister spsrs[5];
  SystemCoproc cp15;
  size_t id;
  uint32_t user_regs[16];
  uint32_t fiq_regs[7];
  uint32_t irq_regs[2];
  uint32_t svc_regs[2];
  uint32_t abt_regs[2];
  uint32_t und_regs[2];
  uint32_t *pc; // = &user_regs[15]

  // true if last instruction modified the pc; must be cleared after each step
  bool jump;
};

extern void init_Processor(Processor*);

extern void destruct_Processor(Processor*);

extern uint32_t *addr_of_reg_m(Processor*, uint8_t reg_id, Mode);

inline uint32_t reg_m(Processor *proc, uint8_t reg_id, Mode m) {
  return *addr_of_reg_m(proc,reg_id,m);
}

inline void set_reg_m(Processor *proc, uint8_t reg_id, Mode m, uint32_t data) {
  *addr_of_reg_m(proc,reg_id,m) = data;
}

inline uint32_t *addr_of_reg(Processor *proc, uint8_t reg_id) {
  return addr_of_reg_m(proc,reg_id,proc->cpsr.mode);
}

inline uint32_t reg(Processor *proc, uint8_t reg_id) {
  return reg_m(proc,reg_id,proc->cpsr.mode);
}

inline void set_reg(Processor *proc, uint8_t reg_id, uint32_t data) {
  return set_reg_m(proc,reg_id,proc->cpsr.mode,data);
}

inline uint32_t inst_size(Processor *proc) {
  return proc->cpsr.T_flag ? 2 : 4;
}

inline void set_pc_raw(Processor *proc, uint32_t new_pc) { // never set thumb/arm32 mode
  assert(!(new_pc&(inst_size(proc)-1)) && "pc misaligned");
  proc->jump = true; *proc->pc = new_pc + 2*inst_size(proc);
}

inline void set_pc(Processor *proc, uint32_t new_pc) { // may set thumb/arm32 mode
  proc->cpsr.T_flag = new_pc&1;
  set_pc_raw(proc, new_pc&~1);
}

inline bool InAPrivilegedMode(Processor *proc) {return proc->cpsr.mode!=usr;}
inline bool CurrentModeHasSPSR(Processor *proc) {return proc->cpsr.mode<sys;}

inline StatusRegister *spsr_m(Processor *proc, Mode m) {
  if (m<sys) return &proc->spsrs[m];
  else ERROR("This mode does not have a SPSR");
}

inline StatusRegister *spsr(Processor *proc) {
  if (CurrentModeHasSPSR(proc)) return &proc->spsrs[proc->cpsr.mode];
  else ERROR("Current mode does not have a SPSR");
}

inline uint32_t address_of_next_instruction(Processor *proc) {
  return *proc->pc - inst_size(proc);
}

inline uint32_t address_of_current_instruction(Processor *proc) {
  return *proc->pc - 2*inst_size(proc);
}

inline bool high_vectors_configured(Processor *proc) {
  return CP15_reg1_Vbit(&proc->cp15);
}

extern void dependent_operation(Processor *proc, uint8_t n);
extern void load(Processor *proc, uint8_t n, uint32_t x);
extern void send(Processor *proc, uint8_t n, uint32_t x);
extern bool NotFinished(Processor *proc, uint8_t n);
extern uint32_t first_value(Processor *proc, uint8_t n);
extern uint32_t second_value(Processor *proc, uint8_t n);
extern uint32_t value(Processor *proc, uint8_t n);
