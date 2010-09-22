/* SimSoC-Cert, a library on processor architectures for embedded systems. */
/* See the COPYRIGHTS and LICENSE files. */

/* The condition field */

#ifndef SLV6_CONDITION_H
#define SLV6_CONDITION_H

#include "common.h"

BEGIN_SIMSOC_NAMESPACE

typedef enum{SLV6_EQ, SLV6_NE, SLV6_CS_HS, SLV6_CC_LO,
             SLV6_MI, SLV6_PL, SLV6_VS,    SLV6_VC,
             SLV6_HI, SLV6_LS, SLV6_GE,    SLV6_LT,
             SLV6_GT, SLV6_LE, SLV6_AL} SLv6_Condition;

extern const char *condition2string(SLv6_Condition);

struct SLv6_StatusRegister;
extern bool ConditionPassed(struct SLv6_StatusRegister*, SLv6_Condition);

END_SIMSOC_NAMESPACE

#endif /* SLV6_CONDITION_H */
