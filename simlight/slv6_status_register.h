/* SimSoC-Cert, a library on processor architectures for embedded systems. */
/* See the COPYRIGHTS and LICENSE files. */

/* Status registers (such as CPSR) */

#ifndef SLV6_STATUS_REGISTER_H
#define SLV6_STATUS_REGISTER_H

#include "slv6_mode.h"
#include "common.h"

BEGIN_SIMSOC_NAMESPACE

struct SLv6_StatusRegister {
  bool N_flag; /* bit 31 */
  bool Z_flag;
  bool C_flag;
  bool V_flag; /* bit 28 */
  bool Q_flag; /* bit 27 */
  bool J_flag; /* bit 24 */
  bool GE0; /* bit 16 */
  bool GE1;
  bool GE2;
  bool GE3; /* bit 19 */
  bool E_flag; /* bit 9 */
  bool A_flag;
  bool I_flag;
  bool F_flag;
  bool T_flag; /* bit 5 */
  SLv6_Mode mode;
  uint32_t background; /* reserved bits */
};

extern uint32_t StatusRegister_to_uint32(struct SLv6_StatusRegister*);
extern void set_StatusRegister(struct SLv6_StatusRegister*, uint32_t);

static inline void set_GE_32(struct SLv6_StatusRegister *sr, uint8_t n) {sr->GE2 = n&1; sr->GE3 = n>>1;}
static inline void set_GE_10(struct SLv6_StatusRegister *sr, uint8_t n) {sr->GE0 = n&1; sr->GE1 = n>>1;}

static inline uint32_t UnallocMask() {return 0x06F0FC00;}
static inline uint32_t UserMask()    {return 0xF80F0200;}
static inline uint32_t PrivMask()    {return 0x000001DF;}
static inline uint32_t StateMask()   {return 0x01000020;}

END_SIMSOC_NAMESPACE

#endif /* SLV6_STATUS_REGISTER_H */
