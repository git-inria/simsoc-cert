/* SimSoC-Cert, a library on processor architectures for embedded systems. */
/* See the COPYRIGHTS and LICENSE files. */

/* Status registers (such as CPSR) */

#ifndef ARM_STATUS_REGISTER_H
#define ARM_STATUS_REGISTER_H

#include "arm_mode.h"
#include "common.h"

struct StatusRegister {
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
  Mode mode;
  uint32_t background; /* reserved bits */
};

extern uint32_t StatusRegister_to_uint32(struct StatusRegister*);
extern void set_StatusRegister(struct StatusRegister*, uint32_t);

inline void set_GE_32(struct StatusRegister *sr, uint8_t n) {sr->GE2 = n&1; sr->GE3 = n>>1;}
inline void set_GE_10(struct StatusRegister *sr, uint8_t n) {sr->GE0 = n&1; sr->GE1 = n>>1;}

inline uint32_t UnallocMask() {return 0x06F0FC00;}
inline uint32_t UserMask()    {return 0xF80F0200;}
inline uint32_t PrivMask()    {return 0x000001DF;}
inline uint32_t StateMask()   {return 0x01000020;}

#endif /* ARM_STATUS_REGISTER_H */
