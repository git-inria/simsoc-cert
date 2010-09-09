/* SimSoC-Cert, a library on processor architectures for embedded systems. */
/* See the COPYRIGHTS and LICENSE files. */

/* The System Control Coprocessor (CP15) */

#ifndef ARM_SYSTEM_COPROC_H
#define ARM_SYSTEM_COPROC_H

#include "common.h"

struct SystemCoproc {
  bool ee_bit;
  bool u_bit;
  bool v_bit;
};

extern void init_CP15(struct SystemCoproc*);

static inline bool CP15_reg1_EEbit(struct SystemCoproc *cp15) {return cp15->ee_bit;}
static inline bool CP15_reg1_Ubit(struct SystemCoproc *cp15) {return cp15->u_bit;}
static inline bool CP15_reg1_Vbit(struct SystemCoproc *cp15) {return cp15->v_bit;}

extern void dependent_operation_CP15(struct SystemCoproc*);
extern void load_CP15(struct SystemCoproc*, uint32_t);
extern void send_CP15(struct SystemCoproc*, uint32_t);
extern bool NotFinished_CP15(struct SystemCoproc*);
extern uint32_t first_value_CP15(struct SystemCoproc*);
extern uint32_t second_value_CP15(struct SystemCoproc*);
extern uint32_t value_CP15(struct SystemCoproc*);

#endif /* ARM_SYSTEM_COPROC_H */
