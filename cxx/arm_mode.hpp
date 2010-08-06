// SimSoC-Cert, a library on processor architectures for embedded systems.
// See the COPYRIGHTS and LICENSE files.

// The modes of an ARM processor

#ifndef ARM_MODE_H
#define ARM_MODE_H

#include "common.hpp"

typedef enum {fiq, irq, svc, abt, und, sys, usr} Mode;

extern bool decode_mode(Mode*, uint32_t);
// return false in case of invalid mode

extern uint32_t encode_mode(Mode);

extern const char *mode2string(Mode);

#endif // ARM_MODE_H
