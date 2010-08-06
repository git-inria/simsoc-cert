// SimSoC-Cert, a library on processor architectures for embedded systems.
// See the COPYRIGHTS and LICENSE files.

// The condition field

#ifndef ARM_CONDITION_H
#define ARM_CONDITION_H

#include "common.hpp"

typedef enum{EQ, NE, CS_HS, CC_LO, MI, PL, VS, VC,
             HI, LS, GE, LT, GT, LE, AL} Condition;

extern const char *condition2string(Condition);

struct StatusRegister;
extern bool ConditionPassed(StatusRegister*, Condition);

#endif // ARM_CONDITION_H
