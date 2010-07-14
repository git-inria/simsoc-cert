// SimSoC-Cert, a library on processor architectures for embedded systems.
// See the COPYRIGHTS and LICENSE files.

// ISS for ARM processors implementing ARM architecture version 6.

// Code for the instructions is generated automatically based on the
// formalization produced by:
// - ../refARMparsing/Makefile
// - ../pseudocode/bin/main -cxx

#ifndef ARM_ISS_BASE_HPP
#define ARM_ISS_BASE_HPP

#include <inttypes.h>
#include <cstdlib>
#include <cassert>
#include <iostream>

#define TODO(msg) do {                                                  \
    std::cout <<std::dec <<"TODO: " <<msg <<"(" __FILE__ ":" <<__LINE__ <<")\n"; \
    abort(); } while (0);
#define ERROR(msg) do {                                                 \
    std::cout <<std::dec <<"ERROR: " <<msg <<"(" __FILE__ ":" <<__LINE__ <<")\n"; \
    abort(); } while (0);

struct ARM_MMU {
  static const uint32_t MEMSTART = 4;
  static const uint32_t MEMSIZE = 0x100000; // 1 MB
  static const uint32_t MEMEND = MEMSTART + MEMSIZE;

  ARM_MMU();
  uint8_t read_byte(uint32_t addr);
  uint16_t read_half(uint32_t addr);
  uint32_t read_word(uint32_t addr);
  void write_byte(uint32_t addr, uint8_t data);
  void write_half(uint32_t addr, uint16_t data);
  void write_word(uint32_t addr, uint32_t data);

protected:
  uint8_t *mem;
};

struct ARM_Coprocessor {
  virtual void dependent_operation() {
    TODO("Coprocessor dependent operation"); }
  virtual void load(uint32_t) {
    TODO("Coprocessor load");}
  virtual void send(uint32_t) {
    TODO("Coprocessor send");}
  virtual bool NotFinished() const {
    TODO("Coprocessor NotFinished"); return false;}
  virtual uint32_t first_value() {
    TODO("Coprocessor first value"); return 0;}
  virtual uint32_t second_value() {
    TODO("Coprocessor second value"); return 0;}
  virtual uint32_t value() {
    TODO("Coprocessor value"); return 0;}
};

struct ARM_SystemCoprocessor: ARM_Coprocessor {
  bool get_reg1_EEbit() const {return 0;} // exception endianness
  bool get_reg1_Ubit()  const {return 0;} // alignement
  bool get_reg1_Vbit()  const {return 0;} // high vectors
};

struct ARM_Processor {
  // types
  typedef enum{EQ, NE, CS_HS, CC_LO, MI, PL, VS, VC,
               HI, LS, GE, LT, GT, LE, AL} Condition;
  typedef enum {fiq, irq, svc, abt, und, sys, usr} Mode;

  struct StatusRegister {
    static const uint32_t reserved_mask = 0x06f0fc00;
    bool N_flag; // bit 31
    bool Z_flag;
    bool C_flag;
    bool V_flag; // bit 28
    bool Q_flag; // bit 27
    bool J_flag; // bit 24
    bool GE0; // bit 16
    bool GE1;
    bool GE2;
    bool GE3; // bit 19
    bool E_flag; // bit 9
    bool A_flag;
    bool I_flag;
    bool F_flag;
    bool T_flag; // bit 5
    Mode mode;
    uint32_t background; // reserved bits

    operator uint32_t () const;
    StatusRegister &operator = (uint32_t value);

    void set_GE_32(uint8_t n) {GE2 = n&1; GE3 = n>>1;}
    void set_GE_10(uint8_t n) {GE0 = n&1; GE1 = n>>1;}
    StatusRegister(uint32_t w) {*this = w;}
    StatusRegister() {*this = 0x1f;}
  };

  // constants
  static const uint8_t PC = 15;
  static const uint8_t LR = 14;
  static const uint8_t SP = 13;

  // members
  ARM_MMU mmu;
  StatusRegister cpsr;
  StatusRegister spsrs[5];
  ARM_SystemCoprocessor cp15;
  size_t id;
  uint32_t user_regs[16];
  uint32_t fiq_regs[7];
  uint32_t irq_regs[2];
  uint32_t svc_regs[2];
  uint32_t abt_regs[2];
  uint32_t und_regs[2];
  bool jump; // true if last instruction modified the pc; must be cleared after each step
  uint32_t &pc;

  // constructor
  ARM_Processor(size_t id);

  // methods
  uint32_t &reg(uint8_t reg_id) {return reg(reg_id,cpsr.mode);}
  const uint32_t &reg(uint8_t reg_id) const {return reg(reg_id,cpsr.mode);}
  uint32_t &reg(uint8_t reg_id, Mode);
  const uint32_t &reg(uint8_t reg_id, Mode) const;

  bool condition_passed(Condition cond) const;

  void set_pc(uint32_t new_pc); // may set thumb/arm32 mode

  void set_pc_raw(uint32_t new_pc) { // never set thumb/arm32 mode
    assert(!(new_pc&(inst_size()-1)) && "pc misaligned");
    jump = true; pc = new_pc+8;
  }

  bool current_mode_has_spsr() const {return cpsr.mode<sys;}

  StatusRegister &spsr() {
    if (current_mode_has_spsr()) return spsrs[cpsr.mode];
    else ERROR("Current mode does not have a SPSR");
  }
  StatusRegister &spsr(Mode m) {
    if (m<sys) return spsrs[m];
    else ERROR("This mode does not have a SPSR");
  }

  ARM_Coprocessor *coproc(uint8_t cp_num) {
    if (cp_num==15) return &cp15; else return NULL;}

  uint32_t inst_size() const {return cpsr.T_flag ? 2 : 4;}

  // static methods
  static uint32_t msr_UnallocMask() {return 0x06F0FC00;}
  static uint32_t msr_UserMask()    {return 0xF80F0200;}
  static uint32_t msr_PrivMask()    {return 0x000001DF;}
  static uint32_t msr_StateMask()   {return 0x01000020;}

  // return false on failure
  static bool decode_mode(uint32_t x, Mode &m);
};

struct ARM_ISS_Base {
  ARM_Processor proc;

  // default constructor
  ARM_ISS_Base(): proc(0) {}

  bool ConditionPassed(ARM_Processor::Condition cond) const {
    return proc.condition_passed(cond);}
  bool CurrentModeHasSPSR() const {return proc.current_mode_has_spsr();}
  static void unpredictable();
  uint32_t address_of_next_instruction() const {return proc.reg(ARM_Processor::PC)-4;}
  uint32_t address_of_current_instruction() const {return proc.reg(ARM_Processor::PC)-8;}

  bool InAPrivilegedMode() const {return proc.cpsr.mode!=ARM_Processor::usr;}
  uint32_t TLB(uint32_t virtual_address) const {return virtual_address;}
  bool Shared(uint32_t) const {return false;}
  bool high_vectors_configured() {return proc.cp15.get_reg1_Vbit();}
  size_t ExecutingProcessor() {return proc.id;}
  void MarkExclusiveGlobal(uint32_t, size_t, uint32_t) {}
  void MarkExclusiveLocal(uint32_t, size_t, uint32_t) {}
  void ClearExclusiveByAddress(uint32_t, size_t, uint32_t) {}
  void ClearExclusiveLocal(size_t) {}
  bool IsExclusiveLocal(uint32_t, size_t, uint32_t) const {return true;}
  bool IsExclusiveGlobal(uint32_t, size_t, uint32_t) const {return true;}

  bool not_overridden_by_debug_hardware() {return true;}
  bool JE_bit_of_Main_Configuration_register() {return false;}
  uint32_t jpc_SUB_ARCHITECTURE_DEFINED_value() {return 0;}
  uint32_t invalidhandler_SUB_ARCHITECTURE_DEFINED_value() {return 0;}
  bool Jazelle_Extension_accepts_opcode_at(uint32_t) {return false;}
  bool CV_bit_of_Jazelle_OS_Control_register() {return false;}
  void Start_opcode_execution_at(uint32_t) {}
  bool IMPLEMENTATION_DEFINED_CONDITION() {return false;}

  static uint32_t bit_position_of_most_significant_1(uint32_t);
  static bool is_even(uint8_t x) {return !(x&1);}
  static uint32_t Number_Of_Set_Bits_In(uint16_t x);

  static bool CarryFrom8_add2(uint8_t, uint8_t);
  static bool CarryFrom16_add2(uint16_t, uint16_t);
  static bool CarryFrom_add2(uint32_t, uint32_t);
  static bool CarryFrom_add3(uint32_t, uint32_t, bool);
  static bool OverflowFrom_add2(uint32_t, uint32_t);
  static bool OverflowFrom_add3(uint32_t a, uint32_t b, bool) {
    return OverflowFrom_add2(a,b);}
  static bool BorrowFrom_sub2(uint8_t, uint8_t);
  static bool BorrowFrom_sub2(uint16_t, uint16_t);
  static bool BorrowFrom_sub2(uint32_t, uint32_t);
  static bool BorrowFrom_sub3(uint32_t, uint32_t, bool);
  static bool OverflowFrom_sub2(uint32_t, uint32_t);
  static bool OverflowFrom_sub3(uint32_t a, uint32_t b, bool) {
    return OverflowFrom_sub2(a,b);}

  static uint32_t SignExtend_30(uint32_t x) {return x&(1<<23) ? 0x7f000000|x : x;}

  static uint32_t SignExtend16(uint16_t x) {
    return static_cast<uint32_t>(static_cast<int32_t>(static_cast<int16_t>(x)));}

  static uint32_t SignExtend8(uint8_t x) {
    return static_cast<uint32_t>(static_cast<int32_t>(static_cast<int8_t>(x)));}

  static uint32_t ZeroExtend(uint32_t x) {return x;}
  static uint32_t NOT(uint32_t x) {return ~x;}
  static uint32_t NOT(bool x) {return !x;}
  static uint32_t rotate_right(uint32_t x, uint32_t n) {
    return (x<<(32-n)) | (x>>n);}

  static uint32_t asr(uint32_t x, uint32_t n) { // FIXME: shift by 32
    return static_cast<uint32_t>(static_cast<int32_t>(x)>>n);}

  static uint16_t get_half_0(uint32_t x) {return x;}
  static uint16_t get_half_1(uint32_t x) {return x>>16;}
  static uint8_t get_byte_0(uint32_t x) {return x;}
  static uint8_t get_byte_1(uint32_t x) {return x>>8;}
  static uint8_t get_byte_2(uint32_t x) {return x>>16;}
  static uint8_t get_byte_3(uint32_t x) {return x>>24;}

  static inline uint32_t get_bits(uint32_t x, uint32_t a, uint32_t b) { // return x[a:b]
    assert(32>a && a>b);
    return (x>>b) & ((1<<(a-b+1))-1);
  }

  static inline uint64_t get_bits64(uint64_t x, size_t a, size_t b) {
    // return x[a:b]
    assert(64>a && a>b);
    return (x>>b) & ((1llu<<(a-b+1))-1);
  }

  static inline bool get_bit(uint32_t x, uint32_t n) { // return x[a]
    return (x>>n)&1;
  }

  static void set_bit(uint32_t &dst, uint32_t num, bool src) {
    if (src) dst |= (1<<num);
    else dst &=~ (1<<num);
  }

  static void set_bit(uint8_t &dst, uint8_t num, bool src) {
    if (src) dst |= (1<<num);
    else dst &=~ (1<<num);
  }

  static void set_field(uint64_t &dst, size_t num1, size_t num, uint64_t src);
  static void set_field(uint32_t &dst, uint32_t num1, uint32_t num, uint32_t src);
  static void set_field(uint8_t &dst, uint8_t num1, uint8_t num, uint8_t src);

  static uint32_t SignedSat_add2(uint32_t a, uint32_t b);
  static uint32_t SignedSat_sub2(uint32_t a, uint32_t b);
  static uint32_t SignedSat_double(uint32_t a);
  static bool SignedDoesSat_add2(uint32_t a, uint32_t b);
  static bool SignedDoesSat_sub2(uint32_t a, uint32_t b);
  static bool SignedDoesSat_double(uint32_t a);

  static uint16_t SignedSat_add2(uint16_t a, uint16_t b);
  static uint16_t SignedSat_sub2(uint16_t a, uint16_t b);
  static uint16_t UnsignedSat_add2(uint16_t a, uint16_t b);
  static uint16_t UnsignedSat_sub2(uint16_t a, uint16_t b);

  static uint8_t SignedSat_add2(uint8_t a, uint8_t b);
  static uint8_t SignedSat_sub2(uint8_t a, uint8_t b);
  static uint8_t UnsignedSat_add2(uint8_t a, uint8_t b);
  static uint8_t UnsignedSat_sub2(uint8_t a, uint8_t b);

  static uint32_t SignedSat(int32_t n, uint32_t size);
  static uint32_t SignedDoesSat(int32_t n, uint32_t size);
  static uint32_t UnsignedSat(int32_t n, uint32_t size);
  static uint32_t UnsignedDoesSat(int32_t n, uint32_t size);

  static bool not_cpy_instr(uint32_t bincode) {
    // values come from arm_iss.cpp, decode_and_exec method, case CPY
    return (bincode&0x0fff0ff0)!=0x01a00000;
  }

  static uint64_t to_64(uint32_t x) {return static_cast<uint64_t>(x);}
  static  int64_t to_64( int32_t x) {return static_cast< int64_t>(x);}
  static uint64_t to_64(uint64_t x) {return x;}
  static  int64_t to_64( int64_t x) {return x;}
  static int16_t to_signed(uint16_t x) {return static_cast<int16_t>(x);}
  static int32_t to_signed(uint32_t x) {return static_cast<int32_t>(x);}
  static int64_t to_signed(uint64_t x) {return static_cast<int64_t>(x);}
  static int16_t to_signed( int16_t x) {return x;}
  static int32_t to_signed( int32_t x) {return x;}
  static int64_t to_signed( int64_t x) {return x;}
};

#endif // ARM_ISS_BASE_HPP
