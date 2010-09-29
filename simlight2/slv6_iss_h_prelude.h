/* SimSoC-Cert, a library on processor architectures for embedded systems. */
/* See the COPYRIGHTS and LICENSE files. */

/* ISS for ARM processors implementing ARM architecture version 6. */

/* This file is used by the generated file "arm_iss.h" */

#include "common.h"
#include "slv6_mode.h"
#include "slv6_condition.h"

BEGIN_SIMSOC_NAMESPACE

struct SLv6_Processor;
struct SLv6_Instruction;

/* next types are used only inside SimSoC */
struct ARMv6_BasicBlock;
struct ARMv6_OptimizedBasicBlock;
struct ARMv6_SetReg {
  SLv6_Condition cond;
  uint8_t d;
  uint32_t data;
};

typedef void (*SemanticsFunction)(struct SLv6_Processor *,
                                  struct SLv6_Instruction *);

extern bool arm_decode_and_exec(struct SLv6_Processor*, uint32_t bincode);
extern void arm_decode_and_store(struct SLv6_Instruction*, uint32_t bincode);
extern bool thumb_decode_and_exec(struct SLv6_Processor*, uint16_t bincode);
extern void thumb_decode_and_store(struct SLv6_Instruction*, uint16_t bincode);

extern bool may_branch(const struct SLv6_Instruction*);
