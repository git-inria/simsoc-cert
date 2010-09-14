/* SimSoC-Cert, a library on processor architectures for embedded systems. */
/* See the COPYRIGHTS and LICENSE files. */

/* Status registers (such as CPSR) */

#include "slv6_status_register.h"
#include "slv6_math.h"

uint32_t StatusRegister_to_uint32(struct SLv6_StatusRegister *sr) {
  uint32_t x = sr->background & UnallocMask();
  if (sr->N_flag) x |= 1<<31;
  if (sr->Z_flag) x |= 1<<30;
  if (sr->C_flag) x |= 1<<29;
  if (sr->V_flag) x |= 1<<28;
  if (sr->Q_flag) x |= 1<<27;
  if (sr->J_flag) x |= 1<<24;
  if (sr->GE0) x |= 1<<16;
  if (sr->GE1) x |= 1<<17;
  if (sr->GE2) x |= 1<<18;
  if (sr->GE3) x |= 1<<19;
  if (sr->E_flag) x |= 1<<9;
  if (sr->A_flag) x |= 1<<8;
  if (sr->I_flag) x |= 1<<7;
  if (sr->F_flag) x |= 1<<6;
  if (sr->T_flag) x |= 1<<5;
  x |= encode_mode(sr->mode);
  return x;
}

void set_StatusRegister(struct SLv6_StatusRegister *sr, uint32_t x) {
  sr->background = x & UnallocMask();
  sr->N_flag = get_bit(x,31);
  sr->Z_flag = get_bit(x,30);
  sr->C_flag = get_bit(x,29);
  sr->V_flag = get_bit(x,28);
  sr->Q_flag = get_bit(x,27);
  sr->J_flag = get_bit(x,24);
  sr->GE0 = get_bit(x,16);
  sr->GE1 = get_bit(x,17);
  sr->GE2 = get_bit(x,18);
  sr->GE3 = get_bit(x,19);
  sr->A_flag = get_bit(x,9);
  sr->E_flag = get_bit(x,8);
  sr->I_flag = get_bit(x,7);
  sr->F_flag = get_bit(x,6);
  sr->T_flag = get_bit(x,5);
  bool ok = decode_mode(&sr->mode,x);
  if (!ok) ERROR("invalid mode");
}
