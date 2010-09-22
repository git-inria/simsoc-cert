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

typedef void (*SemanticsFunction)(struct SLv6_Processor *,
                                  struct SLv6_Instruction *);

extern bool decode_and_exec(struct SLv6_Processor*, uint32_t bincode);
extern void decode_and_store(struct SLv6_Instruction*, uint32_t bincode);

extern bool may_branch(const struct SLv6_Instruction*);
