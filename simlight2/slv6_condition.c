/* SimSoC-Cert, a library on processor architectures for embedded systems. */
/* See the COPYRIGHTS and LICENSE files. */

/* The condition field */

#include "slv6_condition.h"
#include "slv6_status_register.h"

BEGIN_SIMSOC_NAMESPACE

const char *condition2string(SLv6_Condition cond) {
  switch (cond) {
  case SLV6_EQ: return "EQ";
  case SLV6_NE: return "NE";
  case SLV6_CS_HS: return "HS";
  case SLV6_CC_LO: return "LO";
  case SLV6_MI: return "MI";
  case SLV6_PL: return "PL";
  case SLV6_VS: return "VS";
  case SLV6_VC: return "VC";
  case SLV6_HI: return "HI";
  case SLV6_LS: return "LS";
  case SLV6_GE: return "GE";
  case SLV6_LT: return "LT";
  case SLV6_GT: return "GT";
  case SLV6_LE: return "LE";
  case SLV6_AL: return "AL";
  }
  abort();
}

bool ConditionPassed(struct SLv6_StatusRegister *sr, SLv6_Condition cond) {
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

END_SIMSOC_NAMESPACE
