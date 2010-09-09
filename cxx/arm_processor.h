/* SimSoC-Cert, a library on processor architectures for embedded systems. */
/* See the COPYRIGHTS and LICENSE files. */

/* The main class */

#include "common.h"
#include "arm_mmu.h"
#include "arm_mode.h"
#include "arm_status_register.h"
#include "arm_system_coproc.h"
#include <assert.h>

struct Processor {
  struct MMU mmu;
  struct StatusRegister cpsr;
  struct StatusRegister spsrs[5];
  struct SystemCoproc cp15;
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

extern void init_Processor(struct Processor*);

extern void destruct_Processor(struct Processor*);

extern uint32_t *addr_of_reg_m(struct Processor*, uint8_t reg_id, Mode);

static inline uint32_t reg_m(struct Processor *proc, uint8_t reg_id, Mode m) {
  return *addr_of_reg_m(proc,reg_id,m);
}

static inline void set_reg_m(struct Processor *proc, uint8_t reg_id, Mode m, uint32_t data) {
  *addr_of_reg_m(proc,reg_id,m) = data;
}

static inline uint32_t *addr_of_reg(struct Processor *proc, uint8_t reg_id) {
  return addr_of_reg_m(proc,reg_id,proc->cpsr.mode);
}

static inline uint32_t reg(struct Processor *proc, uint8_t reg_id) {
  return reg_m(proc,reg_id,proc->cpsr.mode);
}

static inline void set_reg(struct Processor *proc, uint8_t reg_id, uint32_t data) {
  assert(reg_id!=15);
  return set_reg_m(proc,reg_id,proc->cpsr.mode,data);
}

static inline uint32_t inst_size(struct Processor *proc) {
  return proc->cpsr.T_flag ? 2 : 4;
}

static inline void set_pc_raw(struct Processor *proc, uint32_t new_pc) {
  /* never set thumb/arm32 mode */
  assert(!(new_pc&(inst_size(proc)-1)) && "pc misaligned");
  proc->jump = true; *proc->pc = new_pc + 2*inst_size(proc);
}

static inline void set_reg_or_pc(struct Processor *proc, uint8_t reg_id, uint32_t data) {
  if (reg_id==15)
    set_pc_raw(proc,data);
  else
    set_reg(proc,reg_id,data);
}


static inline void set_pc(struct Processor *proc, uint32_t new_pc) {
  /* may set thumb/arm32 mode */
  proc->cpsr.T_flag = new_pc&1;
  set_pc_raw(proc, new_pc&~1);
}

static inline bool InAPrivilegedMode(struct Processor *proc) {return proc->cpsr.mode!=usr;}
static inline bool CurrentModeHasSPSR(struct Processor *proc) {return proc->cpsr.mode<sys;}

static inline struct StatusRegister *spsr_m(struct Processor *proc, Mode m) {
  if (m<sys) return &proc->spsrs[m];
  else ERROR("This mode does not have a SPSR");
}

static inline struct StatusRegister *spsr(struct Processor *proc) {
  if (CurrentModeHasSPSR(proc)) return &proc->spsrs[proc->cpsr.mode];
  else ERROR("Current mode does not have a SPSR");
}

static inline uint32_t address_of_next_instruction(struct Processor *proc) {
  return *proc->pc - inst_size(proc);
}

static inline uint32_t address_of_current_instruction(struct Processor *proc) {
  return *proc->pc - 2*inst_size(proc);
}

static inline bool high_vectors_configured(struct Processor *proc) {
  return CP15_reg1_Vbit(&proc->cp15);
}

extern void dependent_operation(struct Processor *proc, uint8_t n);
extern void load(struct Processor *proc, uint8_t n, uint32_t x);
extern void send(struct Processor *proc, uint8_t n, uint32_t x);
extern bool NotFinished(struct Processor *proc, uint8_t n);
extern uint32_t first_value(struct Processor *proc, uint8_t n);
extern uint32_t second_value(struct Processor *proc, uint8_t n);
extern uint32_t value(struct Processor *proc, uint8_t n);
