/* SimSoC-Cert, a library on processor architectures for embedded systems. */
/* See the COPYRIGHTS and LICENSE files. */

/* Status registers (SR) */

#ifndef SLSH4_STATUS_REGISTER_H
#define SLSH4_STATUS_REGISTER_H

#include "common.h"

BEGIN_SIMSOC_NAMESPACE

struct SLSH4_StatusRegister {
  bool MD;
  bool RB;
  bool BL;
  bool FD;
  bool M;
  bool Q;
  char IMASK;
  bool S;
  bool T;
};

END_SIMSOC_NAMESPACE

#endif /* SLSH4_STATUS_REGISTER_H */
