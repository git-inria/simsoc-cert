struct SLv6_MMU;

struct SLv6_Processor;

struct SLv6_StatusRegister;

struct SLv6_SystemCoproc;

struct SLv6_MMU {
  unsigned int begin;
  unsigned int size;
  unsigned int end;
  unsigned char *mem;
};
struct SLv6_Processor {
  struct SLv6_MMU *mmu_ptr;
  struct SLv6_StatusRegister cpsr;
  struct SLv6_StatusRegister spsrs[5];
  struct SLv6_SystemCoproc cp15;
  unsigned int id;
  unsigned int user_regs[16];
  unsigned int fiq_regs[7];
  unsigned int irq_regs[2];
  unsigned int svc_regs[2];
  unsigned int abt_regs[2];
  unsigned int und_regs[2];
  unsigned int *pc;
  unsigned char jump;
};
struct SLv6_StatusRegister {
  unsigned char N_flag;
  unsigned char Z_flag;
  unsigned char C_flag;
  unsigned char V_flag;
  unsigned char Q_flag;
  unsigned char J_flag;
  unsigned char GE0;
  unsigned char GE1;
  unsigned char GE2;
  unsigned char GE3;
  unsigned char E_flag;
  unsigned char A_flag;
  unsigned char I_flag;
  unsigned char F_flag;
  unsigned char T_flag;
  int mode;
  unsigned int background;
};
struct SLv6_SystemCoproc {
  unsigned char ee_bit;
  unsigned char u_bit;
  unsigned char v_bit;
};
unsigned char const __stringlit_6[71] = "ERROR: simulating something unpredictable (../arm6/simlight/adc.c:%d)\012";

unsigned char const __stringlit_3[49] = "!(new_pc&(inst_size(proc)-1)) && \042pc misaligned\042";

unsigned char const __stringlit_2[11] = "reg_id!=15";

unsigned char const __stringlit_4[14] = "pc misaligned";

unsigned char const __stringlit_5[81] = "ERROR: Current mode does not have a SPSR (../arm6/simlight/slv6_processor.h:%d)\012";

unsigned char const __stringlit_1[34] = "../arm6/simlight/slv6_processor.h";

extern int printf$ii(void *, void *);

extern double __builtin_fabs(double);

extern unsigned char __builtin_volatile_read_int8unsigned(void *);

extern signed char __builtin_volatile_read_int8signed(void *);

extern unsigned short __builtin_volatile_read_int16unsigned(void *);

extern short __builtin_volatile_read_int16signed(void *);

extern int __builtin_volatile_read_int32(void *);

extern float __builtin_volatile_read_float32(void *);

extern double __builtin_volatile_read_float64(void *);

extern void *__builtin_volatile_read_pointer(void *);

extern void __builtin_volatile_write_int8unsigned(void *, unsigned char);

extern void __builtin_volatile_write_int8signed(void *, signed char);

extern void __builtin_volatile_write_int16unsigned(void *, unsigned short);

extern void __builtin_volatile_write_int16signed(void *, short);

extern void __builtin_volatile_write_int32(void *, int);

extern void __builtin_volatile_write_float32(void *, float);

extern void __builtin_volatile_write_float64(void *, double);

extern void __builtin_volatile_write_pointer(void *, void *);

extern void __builtin_memcpy(void *, void *, unsigned int);

extern void __builtin_memcpy_words(void *, void *, unsigned int);

extern void __builtin_annotation(unsigned char *);

extern double __builtin_fsqrt(double);

extern double __builtin_fmax(double, double);

extern double __builtin_fmin(double, double);

extern void abort(void);

extern void __assert_fail(unsigned char *, unsigned char *, unsigned int, unsigned char *);

extern unsigned char ConditionPassed(struct SLv6_StatusRegister *, int);

extern void copy_StatusRegister(struct SLv6_StatusRegister *, struct SLv6_StatusRegister *);

extern unsigned int *addr_of_reg_m(struct SLv6_Processor *, unsigned char, int);

unsigned int reg_m(struct SLv6_Processor *proc, unsigned char reg_id, int m)
{
  return *addr_of_reg_m(proc, reg_id, m);
}

void set_reg_m(struct SLv6_Processor *proc, unsigned char reg_id, int m, unsigned int data)
{
  *addr_of_reg_m(proc, reg_id, m) = data;
}

unsigned int reg(struct SLv6_Processor *proc, unsigned char reg_id)
{
  return reg_m(proc, reg_id, (*proc).cpsr.mode);
}

void set_reg(struct SLv6_Processor *proc, unsigned char reg_id, unsigned int data)
{
  reg_id != 15 ? (void) 0
    : __assert_fail(__stringlit_2, __stringlit_1, 58, (unsigned char *) 0);
  set_reg_m(proc, reg_id, (*proc).cpsr.mode, data);
}

unsigned int inst_size(struct SLv6_Processor *proc)
{
  return (*proc).cpsr.T_flag ? 2 : 4;
}

void set_pc_raw(struct SLv6_Processor *proc, unsigned int new_pc)
{
  (!(new_pc & inst_size(proc) - 1) ? (__stringlit_4 ? 1 : 0) : 0) ? (void) 0
    : __assert_fail(__stringlit_3, __stringlit_1, 68, (unsigned char *) 0);
  (*proc).jump = 1;
  *(*proc).pc = new_pc + 2 * inst_size(proc);
}

void set_reg_or_pc(struct SLv6_Processor *proc, unsigned char reg_id, unsigned int data)
{
  if (reg_id == 15) {
    set_pc_raw(proc, data);
  } else {
    set_reg(proc, reg_id, data);
  }
}

unsigned char CurrentModeHasSPSR(struct SLv6_Processor *proc)
{
  return (*proc).cpsr.mode < 5;
}

struct SLv6_StatusRegister *spsr(struct SLv6_Processor *proc)
{
  if (CurrentModeHasSPSR(proc)) {
    return &*((*proc).spsrs + (*proc).cpsr.mode);
  } else {
    do {
      printf$ii(__stringlit_5, 97);
      abort();
    } while(0);
  }
  abort();
}

unsigned char CarryFrom_add2(unsigned int a, unsigned int b)
{
  return a + b < a;
}

unsigned char CarryFrom_add3(unsigned int a, unsigned int b, unsigned int c)
{
  return CarryFrom_add2(a, b) ? 1 : (CarryFrom_add2(a + b, c) ? 1 : 0);
}

unsigned char OverflowFrom_add2(unsigned int a, unsigned int b)
{
  unsigned int r;
  r = a + b;
  return ((a ^ ~b) & (a ^ r)) >> 31;
}

unsigned char OverflowFrom_add3(unsigned int a, unsigned int b, unsigned char unused)
{
  return OverflowFrom_add2(a, b);
}

unsigned char get_bit(unsigned int x, unsigned int n)
{
  return x >> n & 1;
}

void ADC(struct SLv6_Processor *proc, unsigned char S, int cond, unsigned char d, unsigned char n, unsigned int shifter_operand)
{
  unsigned int old_Rn;
  old_Rn = reg(proc, n);
  if (ConditionPassed(&(*proc).cpsr, cond)) {
    set_reg_or_pc(proc, d, old_Rn + shifter_operand + (*proc).cpsr.C_flag);
    if (S == 1 ? (d == 15 ? 1 : 0) : 0) {
      if (CurrentModeHasSPSR(proc)) {
        copy_StatusRegister(&(*proc).cpsr, spsr(proc));
      } else {
        do {
          printf$ii(__stringlit_6, 19);
          abort();
        } while(0);
      }
    } else {
      if (S == 1) {
        (*proc).cpsr.N_flag = get_bit(reg(proc, d), 31);
        (*proc).cpsr.Z_flag = reg(proc, d) == 0 ? 1 : 0;
        (*proc).cpsr.C_flag =
          CarryFrom_add3(old_Rn, shifter_operand, (*proc).cpsr.C_flag);
        (*proc).cpsr.V_flag =
          OverflowFrom_add3(old_Rn, shifter_operand, (*proc).cpsr.C_flag);
      }
    }
  }
}


