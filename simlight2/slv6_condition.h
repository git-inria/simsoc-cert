/* SimSoC-Cert, a library on processor architectures for embedded systems. */
/* See the COPYRIGHTS and LICENSE files. */

/* The condition field */

#ifndef SLV6_CONDITION_H
#define SLV6_CONDITION_H

#include "common.h"
#include "slv6_status_register.h"
#include <stdio.h>

BEGIN_SIMSOC_NAMESPACE

typedef enum{SLV6_EQ, SLV6_NE, SLV6_CS_HS, SLV6_CC_LO,
             SLV6_MI, SLV6_PL, SLV6_VS,    SLV6_VC,
             SLV6_HI, SLV6_LS, SLV6_GE,    SLV6_LT,
             SLV6_GT, SLV6_LE, SLV6_AL} SLv6_Condition;

extern const char *condition2string(SLv6_Condition);

struct SLv6_StatusRegister;

static inline bool ConditionPassed(struct SLv6_StatusRegister *sr, SLv6_Condition cond) {
  switch (cond) {
  case SLV6_EQ: return sr->Z_flag;
  case SLV6_NE: return !sr->Z_flag;
  case SLV6_CS_HS: return sr->C_flag;
  case SLV6_CC_LO: return !sr->C_flag;
  case SLV6_MI: return sr->N_flag;
  case SLV6_PL: return !sr->N_flag;
  case SLV6_VS: return sr->V_flag;
  case SLV6_VC: return !sr->V_flag;
  case SLV6_HI: return sr->C_flag && !sr->Z_flag;
  case SLV6_LS: return !sr->C_flag || sr->Z_flag;
  case SLV6_GE: return sr->N_flag == sr->V_flag;
  case SLV6_LT: return sr->N_flag != sr->V_flag;
  case SLV6_GT: return !sr->Z_flag && sr->N_flag == sr->V_flag;
  case SLV6_LE: return sr->Z_flag || sr->N_flag != sr->V_flag;
  case SLV6_AL: return true;
  }
  assert(false && "invalid cond"); abort();
}

extern void slv6_print_cond(FILE *f, SLv6_Condition c);

END_SIMSOC_NAMESPACE

#endif /* SLV6_CONDITION_H */
