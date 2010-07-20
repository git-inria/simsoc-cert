// SimSoC-Cert, a library on processor architectures for embedded systems.
// See the COPYRIGHTS and LICENSE files.

// ISS for ARM processors implementing ARM architecture version 6.

// Code for the instructions is generated automatically based on the
// formalization produced by:
// - ../refARMparsing/Makefile
// - ../pseudocode/bin/main -cxx

#include "arm_iss_base.hpp"
#include "common.hpp"
#include <cstring>

using namespace std;

ARM_MMU::ARM_MMU():
  mem(new uint8_t[MEMSIZE])
{
  assert((MEMSTART&3)==0 && "memory start not aligned on a word boundary");
  assert((MEMSIZE&3)==0 && "memory size not aligned on a word boundary");
}

uint8_t ARM_MMU::read_byte(uint32_t addr) {
  assert(MEMSTART<=addr && addr<MEMEND && "out of memory access");
  DEBUG(<<"read byte " <<hex <<(uint32_t)mem[addr-MEMSTART]
        <<" from " <<addr <<'\n');
  return mem[addr-MEMSTART];
}

uint16_t ARM_MMU::read_half(uint32_t addr) {
  assert(MEMSTART<=addr && addr<MEMEND && "out of memory access");
  assert((addr&1)==0 && "misaligned acces");
  union {
    uint16_t half;
    uint8_t bytes[2];
  } tmp;
  memcpy(tmp.bytes,mem+(addr-MEMSTART),2);
  DEBUG(<<"read half " <<hex <<tmp.half <<" from " <<addr <<'\n');
  return tmp.half;
}

uint32_t ARM_MMU::read_word(uint32_t addr) {
  assert(MEMSTART<=addr && addr<MEMEND && "out of memory access");
  assert((addr&3)==0 && "misaligned acces");
  union {
    uint32_t word;
    uint8_t bytes[4];
  } tmp;
  memcpy(tmp.bytes,mem+(addr-MEMSTART),4);
  DEBUG(<<"read " <<hex <<tmp.word <<" from " <<addr <<'\n');
  return tmp.word;
}

void ARM_MMU::write_byte(uint32_t addr, uint8_t data) {
  assert(MEMSTART<=addr && addr<MEMEND && "out of memory access");
  mem[addr-MEMSTART] = data;
  DEBUG(<<"write byte " <<hex <<(uint32_t) data <<" to " <<addr <<'\n');
}

void ARM_MMU::write_half(uint32_t addr, uint16_t data) {
  assert(MEMSTART<=addr && addr<MEMEND && "out of memory access");
  assert((addr&1)==0 && "misaligned acces");
  union {
    uint16_t half;
    uint8_t bytes[2];
  } tmp;
  tmp.half = data;
  memcpy(mem+(addr-MEMSTART),tmp.bytes,2);
  DEBUG(<<"write half " <<hex <<tmp.half <<" to " <<addr <<'\n');
}

void ARM_MMU::write_word(uint32_t addr, uint32_t data) {
  assert(MEMSTART<=addr && addr<MEMEND && "out of memory access");
  assert((addr&3)==0 && "misaligned acces");
  union {
    uint32_t word;
    uint8_t bytes[4];
  } tmp;
  tmp.word = data;
  memcpy(mem+(addr-MEMSTART),tmp.bytes,4);
  DEBUG(<<"write " <<hex <<tmp.word <<" to " <<addr <<'\n');
}

ARM_Processor::StatusRegister::operator uint32_t () const {
  uint32_t x = background & reserved_mask;
  if (N_flag) x |= 1<<31;
  if (Z_flag) x |= 1<<30;
  if (C_flag) x |= 1<<29;
  if (V_flag) x |= 1<<28;
  if (Q_flag) x |= 1<<27;
  if (J_flag) x |= 1<<24;
  if (GE0) x |= 1<<16;
  if (GE1) x |= 1<<17;
  if (GE2) x |= 1<<18;
  if (GE3) x |= 1<<19;
  if (E_flag) x |= 1<<9;
  if (A_flag) x |= 1<<8;
  if (I_flag) x |= 1<<7;
  if (F_flag) x |= 1<<6;
  if (T_flag) x |= 1<<5;
  switch (mode) {
  case fiq: x |= 0x11; break;
  case irq: x |= 0x12; break;
  case svc: x |= 0x13; break;
  case abt: x |= 0x17; break;
  case und: x |= 0x1b; break;
  case sys: x |= 0x1f; break;
  case usr: x |= 0x10; break;
  }
  return x;
}

ARM_Processor::StatusRegister &ARM_Processor::StatusRegister::operator = (uint32_t x) {
  background = x&reserved_mask;
  N_flag = x&(1<<31);
  Z_flag = x&(1<<30);
  C_flag = x&(1<<29);
  V_flag = x&(1<<28);
  Q_flag = x&(1<<27);
  J_flag = x&(1<<24);
  GE0 = x&(1<<16);
  GE1 = x&(1<<17);
  GE2 = x&(1<<18);
  GE3 = x&(1<<19);
  A_flag = x&(1<<9);
  E_flag = x&(1<<8);
  I_flag = x&(1<<7);
  F_flag = x&(1<<6);
  T_flag = x&(1<<5);
  bool ok = decode_mode(x,mode);
  if (!ok) ERROR("invalid mode");
  return *this;
}

ARM_Processor::ARM_Processor(size_t id_):
  mmu(),
  cpsr(0x1df), // = 0b111011111 = A+I+F+System
  cp15(),
  id(id_),
  jump(false),
  pc(user_regs[PC])
{
  // init registers to 0
  int i = 0;
  for (;i<2;++i)
    user_regs[i] = fiq_regs[i] = irq_regs[i] = svc_regs[i] =
      abt_regs[i] = und_regs[i] = 0;
  for (;i<7;++i)
    user_regs[i] = fiq_regs[i] = 0;
  for (;i<16;++i)
    user_regs[i] = 0;
}

uint32_t &ARM_Processor::reg(uint8_t reg_id, Mode m) {
  switch (m) {
  case fiq:
    return (8<=reg_id && reg_id<=14) ? fiq_regs[reg_id-8] : user_regs[reg_id];
  case irq:
    return (13<=reg_id && reg_id<=14) ? irq_regs[reg_id-13] : user_regs[reg_id];
  case svc:
    return (13<=reg_id && reg_id<=14) ? svc_regs[reg_id-13] : user_regs[reg_id];
  case abt:
    return (13<=reg_id && reg_id<=14) ? abt_regs[reg_id-13] : user_regs[reg_id];
  case und:
    return (13<=reg_id && reg_id<=14) ? und_regs[reg_id-13] : user_regs[reg_id];
  case sys: // no break;
  case usr:
    return user_regs[reg_id];
  }
  abort();
}

const uint32_t &ARM_Processor::reg(uint8_t reg_id, Mode m) const {
  switch (m) {
  case fiq:
    return (8<=reg_id && reg_id<=14) ? fiq_regs[reg_id-8] : user_regs[reg_id];
  case irq:
    return (13<=reg_id && reg_id<=14) ? irq_regs[reg_id-13] : user_regs[reg_id];
  case svc:
    return (13<=reg_id && reg_id<=14) ? svc_regs[reg_id-13] : user_regs[reg_id];
  case abt:
    return (13<=reg_id && reg_id<=14) ? abt_regs[reg_id-13] : user_regs[reg_id];
  case und:
    return (13<=reg_id && reg_id<=14) ? und_regs[reg_id-13] : user_regs[reg_id];
  case sys: // no break;
  case usr:
    return user_regs[reg_id];
  }
  abort();
}

bool ARM_Processor::condition_passed(Condition cond) const {
  switch (cond) {
  case EQ: return cpsr.Z_flag;
  case NE: return !cpsr.Z_flag;
  case CS_HS: return cpsr.C_flag;
  case CC_LO: return !cpsr.C_flag;
  case MI: return cpsr.N_flag;
  case PL: return !cpsr.N_flag;
  case VS: return cpsr.V_flag;
  case VC: return !cpsr.V_flag;
  case HI: return cpsr.C_flag && !cpsr.Z_flag;
  case LS: return !cpsr.C_flag || cpsr.Z_flag;
  case GE: return cpsr.N_flag == cpsr.V_flag;
  case LT: return cpsr.N_flag != cpsr.V_flag;
  case GT: return !cpsr.Z_flag && cpsr.N_flag == cpsr.V_flag;
  case LE: return cpsr.Z_flag || cpsr.N_flag != cpsr.V_flag;
  case AL: return true;
  }
  assert(false && "invalid cond"); return false;
}

void ARM_Processor::set_pc(uint32_t new_pc) {
  cpsr.T_flag = new_pc&1;
  set_pc_raw(new_pc);
}

bool ARM_Processor::decode_mode(uint32_t x, Mode &mode) {
  switch (x&0x1f) {
  case 0x11: mode = fiq; return true;
  case 0x12: mode = irq; return true;
  case 0x13: mode = svc; return true;
  case 0x17: mode = abt; return true;
  case 0x1b: mode = und; return true;
  case 0x1f: mode = sys; return true;
  case 0x10: mode = usr; return true;
  default: return false;
  }
}

void ARM_ISS_Base::unpredictable() {
  std::cout <<"Error: simulating something unpredictable.\n";
  exit(1);
}

uint32_t ARM_ISS_Base::bit_position_of_most_significant_1(uint32_t x) {
  for (int32_t n=31; n>=0; --n)
    if (x&(1<<n))
      return n;
  assert(false && "x is zero");
  return ~0;
}

bool ARM_ISS_Base::CarryFrom8_add2(uint32_t a, uint32_t b) {return a+b>0xff;}
bool ARM_ISS_Base::CarryFrom16_add2(uint32_t a, uint32_t b) {return a+b>0xffff;}
bool ARM_ISS_Base::CarryFrom_add2(uint32_t a, uint32_t b) {return (a+b)<a;}

bool ARM_ISS_Base::CarryFrom_add3(uint32_t a, uint32_t b, bool c) {
  return CarryFrom_add2(a,b) || CarryFrom_add2(a+b,c);
}

bool ARM_ISS_Base::OverflowFrom_add2(uint32_t a, uint32_t b) {
  const uint32_t r = a+b;
  return ((a^~b)&(a^r))>>31;
}

bool ARM_ISS_Base::OverflowFrom_sub2(uint32_t a, uint32_t b) {
  const uint32_t r = a-b;
  return ((a^b)&(a^r))>>31;
}

bool ARM_ISS_Base::BorrowFrom_sub2(uint32_t a, uint32_t b) {return a<b;}

bool ARM_ISS_Base::BorrowFrom_sub3(uint32_t a, uint32_t b, bool c) {
  return BorrowFrom_sub2(a,b) || BorrowFrom_sub2(a-b,c);
}

uint32_t ARM_ISS_Base::Number_Of_Set_Bits_In(uint16_t x) {
  uint32_t count = 0;
  while (x) {
    count += x&1;
    x >>= 1;
  }
  return count;
}

void ARM_ISS_Base::set_field(uint32_t &dst, uint32_t a, uint32_t b, uint32_t src) {
  assert(a>b);
  const uint32_t mask = ((1<<(a-b))-1)<<b;
  dst &= ~mask;
  dst |= src<<b;
}

uint32_t ARM_ISS_Base::SignedSat32_add(int32_t a, int32_t b) {
  return SignedSat((int64_t)a + (int64_t)b,32);
}
uint32_t ARM_ISS_Base::SignedSat32_sub(int32_t a, int32_t b) {
  return SignedSat((int64_t)a - (int64_t)b,32);
}
uint32_t ARM_ISS_Base::SignedSat32_double(int32_t a) {
  return SignedSat(2*(int64_t)a,32);
}
bool ARM_ISS_Base::SignedDoesSat32_add(int32_t a, int32_t b) {
  return SignedDoesSat((int64_t)a + (int64_t)b,32);
}
bool ARM_ISS_Base::SignedDoesSat32_sub(int32_t a, int32_t b) {
  return SignedDoesSat((int64_t)a - (int64_t)b,32);
}
bool ARM_ISS_Base::SignedDoesSat32_double(int32_t a) {
  return SignedDoesSat(2*(int64_t)a,32);
}

uint32_t ARM_ISS_Base::SignedSat(int64_t x, uint32_t n) {
  if (x < -(1<<(n-1))) return -(1<<(n-1));
  if (x > (1<<(n-1))-1) return (1<<(n-1))-1;
  return x;
}

uint32_t ARM_ISS_Base::SignedDoesSat(int64_t x, uint32_t n) {
  return x < -(1<<(n-1)) || x > (1<<(n-1))-1;
}

uint32_t ARM_ISS_Base::UnsignedSat(int32_t x, uint32_t n) {
  assert(n<32);
  if (x < 0) return 0;
  if (x > (1<<n)-1) return (1<<n)-1;
  return x;
}

uint32_t ARM_ISS_Base::UnsignedDoesSat(int32_t x, uint32_t n) {
  assert(n<32);
  return x < 0 || x > (1<<n)-1;
}
