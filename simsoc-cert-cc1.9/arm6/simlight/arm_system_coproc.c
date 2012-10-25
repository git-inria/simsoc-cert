/* SimSoC-Cert, a library on processor architectures for embedded systems. */
/* See the COPYRIGHTS and LICENSE files. */

/* The System Control Coprocessor (CP15) */

#include "arm_system_coproc.h"

void init_CP15(struct SLv6_SystemCoproc *cp15) {
  cp15->ee_bit = false;
  cp15->u_bit = false;
  cp15->v_bit = false;
}

void dependent_operation_CP15(struct SLv6_SystemCoproc *a) {
  TODO("Coprocessor 15 dependent operation");
}

void load_CP15(struct SLv6_SystemCoproc *a, uint32_t b) {
  TODO("Coprocessor 15 load");
}

void send_CP15(struct SLv6_SystemCoproc *a, uint32_t b) {
  TODO("Coprocessor 15 send");
}

bool NotFinished_CP15(struct SLv6_SystemCoproc *a) {
  TODO("Coprocessor 15 NotFinished"); return false;
}

uint32_t first_value_CP15(struct SLv6_SystemCoproc *a) {
  TODO("Coprocessor 15 first value"); return 0;
}

uint32_t second_value_CP15(struct SLv6_SystemCoproc *a) {
  TODO("Coprocessor 15 second value"); return 0;
}

uint32_t value_CP15(struct SLv6_SystemCoproc *a) {
  TODO("Coprocessor 15 value"); return 0;
}
