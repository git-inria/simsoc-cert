/* SimSoC-Cert, a library on processor architectures for embedded systems. */
/* See the COPYRIGHTS and LICENSE files. */

/* The condition field */

#ifndef SLV6_CONDITION_H
#define SLV6_CONDITION_H

#include "common.h"

BEGIN_SIMSOC_NAMESPACE

typedef enum{EQ, NE, CS_HS, CC_LO, MI, PL, VS, VC,
             HI, LS, GE, LT, GT, LE, AL} SLv6_Condition;

extern const char *condition2string(SLv6_Condition);

struct SLv6_StatusRegister;
extern bool ConditionPassed(struct SLv6_StatusRegister*, SLv6_Condition);

END_SIMSOC_NAMESPACE

#endif /* SLV6_CONDITION_H */
