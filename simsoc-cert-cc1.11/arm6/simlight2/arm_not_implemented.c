/* SimSoC-Cert, a library on processor architectures for embedded systems. */
/* See the COPYRIGHTS and LICENSE files. */

#include "arm_not_implemented.h"

bool slv6_CDP_dependent_operation(struct SLv6_Processor *proc, uint8_t n) {
  TODO("coprocessor dependent_operation");
}

bool slv6_MCR_send(struct SLv6_Processor *proc, uint8_t n,
                   uint8_t opcode_1, uint8_t opcode_2,
                   uint8_t CRn, uint8_t CRm, uint32_t Rd) {
  TODO("coprocessor send");
}

bool slv6_MCRR_send(struct SLv6_Processor *proc, uint8_t n, uint32_t x) {
  TODO("coprocessor send");
}

bool slv6_MRRC_first_value(struct SLv6_Processor *proc,
                           uint32_t *result, uint8_t n) {
  TODO("coprocessor first_value");
}

bool slv6_MRRC_second_value(struct SLv6_Processor *proc,
                                   uint32_t *result, uint8_t n) {
  TODO("coprocessor second_value");
}

bool slv6_MRC_value(struct SLv6_Processor *proc, uint32_t *result, uint8_t n,
                           uint8_t opcode_1, uint8_t opcode_2,
                           uint8_t CRn, uint8_t CRm) {
  TODO("coprocessor value");
}
