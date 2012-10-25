/* SimSoC-Cert, a library on processor architectures for embedded systems. */
/* See the COPYRIGHTS and LICENSE files. */

/* The main class */

#include "slsh4_processor.h"

BEGIN_SIMSOC_NAMESPACE

void init_Processor(struct SLSH4_Processor *proc, struct SLSH4_MMU *m) {
  proc->mmu_ptr = m;
  proc->delayed = false;
  proc->pc = 0xa0000000;
  proc->VBR = 0x00000000;

  proc->SR.MD = 1;
  proc->SR.RB = 1;
  proc->SR.BL = 1;
  proc->SR.FD = 0;
  proc->SR.IMASK = 0xf;

  proc->EXPEVT = 0;
  proc->FPSCR = 0x00040001;
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

void set_bit_1(uint32_t * t, bool n, uint32_t nb) {
  if (n)
    *t |= (1 << nb);
  else
    *t &= ~(1 << nb);
}

void set_bit_4(uint32_t * t, char n, uint32_t nb) {
  *t &= ~(0xF << nb);
  if (n != 0)
    *t |= (n << nb);
  else
    return;
}

uint32_t reg_sr(struct SLSH4_Processor *proc) {
  uint32_t t;
  set_bit_1(&t, proc->SR.MD, 30);
  set_bit_1(&t, proc->SR.RB, 29);
  set_bit_1(&t, proc->SR.BL, 28);
  set_bit_1(&t, proc->SR.FD, 15);
  set_bit_1(&t, proc->SR.M, 9);
  set_bit_1(&t, proc->SR.Q, 8);
  set_bit_4(&t, proc->SR.IMASK, 4);
  set_bit_1(&t, proc->SR.S, 1);
  set_bit_1(&t, proc->SR.T, 0);
  return t;
}

void set_bit_adr_1(bool * n, uint32_t nb, uint32_t data) {
  *n = (data >> nb) & 1; // syntax unsupported by CompCert : 0b1;
}

void set_bit_adr_4(char * n, uint32_t nb, uint32_t data) {
  *n = (data >> nb) & 0xF; // syntax unsupported by CompCert : 0b1111;
}

void set_reg_sr(struct SLSH4_Processor *proc, uint32_t data) {
  set_bit_adr_1(&(proc->SR.MD), 30, data);
  set_bit_adr_1(&(proc->SR.RB), 29, data);
  set_bit_adr_1(&(proc->SR.BL), 28, data);
  set_bit_adr_1(&(proc->SR.FD), 15, data);
  set_bit_adr_1(&(proc->SR.M), 9, data);
  set_bit_adr_1(&(proc->SR.Q), 8, data);
  set_bit_adr_4(&(proc->SR.IMASK), 4, data);
  set_bit_adr_1(&(proc->SR.S), 1, data);
  set_bit_adr_1(&(proc->SR.T), 0, data);
}

uint32_t reg_ssr(struct SLSH4_Processor *proc) {
  uint32_t t;
  set_bit_1(&t, proc->SSR.MD, 30);
  set_bit_1(&t, proc->SSR.RB, 29);
  set_bit_1(&t, proc->SSR.BL, 28);
  set_bit_1(&t, proc->SSR.FD, 15);
  set_bit_1(&t, proc->SSR.M, 9);
  set_bit_1(&t, proc->SSR.Q, 8);
  set_bit_4(&t, proc->SSR.IMASK, 4);
  set_bit_1(&t, proc->SSR.S, 1);
  set_bit_1(&t, proc->SSR.T, 0);
  return t;
}

void set_reg_ssr(struct SLSH4_Processor *proc, uint32_t data) {
  set_bit_adr_1(&(proc->SSR.MD), 30, data);
  set_bit_adr_1(&(proc->SSR.RB), 29, data);
  set_bit_adr_1(&(proc->SSR.BL), 28, data);
  set_bit_adr_1(&(proc->SSR.FD), 15, data);
  set_bit_adr_1(&(proc->SSR.M), 9, data);
  set_bit_adr_1(&(proc->SSR.Q), 8, data);
  set_bit_adr_4(&(proc->SSR.IMASK), 4, data);
  set_bit_adr_1(&(proc->SSR.S), 1, data);
  set_bit_adr_1(&(proc->SSR.T), 0, data);
}

void Delay_Slot(struct SLSH4_Processor *proc, uint32_t addr) {
  proc->delayed = true;
  proc->slot_pc = addr;
}

END_SIMSOC_NAMESPACE
