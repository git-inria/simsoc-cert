/* SimSoC-Cert, a library on processor architectures for embedded systems. */
/* See the COPYRIGHTS and LICENSE files. */

/* The condition field */

#include "arm_condition.h"
#include "arm_status_register.h"
#include "assert.h"

const char *condition2string(Condition cond) {
  switch (cond) {
  case EQ: return "EQ";
  case NE: return "NE";
  case CS_HS: return "HS";
  case CC_LO: return "LO";
  case MI: return "MI";
  case PL: return "PL";
  case VS: return "VS";
  case VC: return "VC";
  case HI: return "HI";
  case LS: return "LS";
  case GE: return "GE";
  case LT: return "LT";
  case GT: return "GT";
  case LE: return "LE";
  case AL: return "AL";
  }
  abort();
}

bool ConditionPassed(struct StatusRegister *sr, Condition cond) {
  switch (cond) {
  case EQ: return sr->Z_flag;
  case NE: return !sr->Z_flag;
  case CS_HS: return sr->C_flag;
  case CC_LO: return !sr->C_flag;
  case MI: return sr->N_flag;
  case PL: return !sr->N_flag;
  case VS: return sr->V_flag;
  case VC: return !sr->V_flag;
  case HI: return sr->C_flag && !sr->Z_flag;
  case LS: return !sr->C_flag || sr->Z_flag;
  case GE: return sr->N_flag == sr->V_flag;
  case LT: return sr->N_flag != sr->V_flag;
  case GT: return !sr->Z_flag && sr->N_flag == sr->V_flag;
  case LE: return sr->Z_flag || sr->N_flag != sr->V_flag;
  case AL: return true;
  }
  assert(false && "invalid cond"); abort();
}
