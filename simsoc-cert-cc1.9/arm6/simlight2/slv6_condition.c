/* SimSoC-Cert, a library on processor architectures for embedded systems. */
/* See the COPYRIGHTS and LICENSE files. */

/* The condition field */

#include "slv6_condition.h"

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

void slv6_print_cond(FILE *f, SLv6_Condition cond) {
  fprintf(f,"%s",condition2string(cond));
}

END_SIMSOC_NAMESPACE
