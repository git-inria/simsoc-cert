/* SimSoC-Cert, a library on processor architectures for embedded systems. */
/* See the COPYRIGHTS and LICENSE files. */

/* Arithmetic and logic functions. */

#ifndef ARM_MATH_H
#define ARM_MATH_H

#include "common.h"

#include "int64_native.h"
#include "int64_emul.h"

BEGIN_SIMSOC_NAMESPACE

extern uint32_t bit_position_of_most_significant_1(uint32_t x);
extern uint32_t Number_Of_Set_Bits_In(uint32_t x);

static inline uint32_t get_half_0(uint32_t x) {return 0xffff&x;}
static inline uint32_t get_half_1(uint32_t x) {return 0xffff&(x>>16);}
static inline uint32_t get_byte_0(uint32_t x) {return 0xff&x;}
static inline uint32_t get_byte_1(uint32_t x) {return 0xff&(x>>8);}
static inline uint32_t get_byte_2(uint32_t x) {return 0xff&(x>>16);}
static inline uint32_t get_byte_3(uint32_t x) {return 0xff&(x>>24);}

static inline int32_t u16_to_i32(uint16_t x) {return (int32_t)(int16_t) x;}
static inline int32_t u8_to_i32(uint8_t x) {return (int32_t)(int8_t) x;}
static inline int32_t get_signed_half_0(uint32_t x) {return u16_to_i32(0xffff&x);}
static inline int32_t get_signed_half_1(uint32_t x) {return u16_to_i32(0xffff&(x>>16));}
static inline int32_t get_signed_byte_0(uint32_t x) {return u8_to_i32(0xff&x);}
static inline int32_t get_signed_byte_1(uint32_t x) {return u8_to_i32(0xff&(x>>8));}
static inline int32_t get_signed_byte_2(uint32_t x) {return u8_to_i32(0xff&(x>>16));}
static inline int32_t get_signed_byte_3(uint32_t x) {return u8_to_i32(0xff&(x>>24));}

static inline bool is_even(uint8_t x) {return !(x&1);}

static inline bool CarryFrom8_add2(uint32_t a, uint32_t b) {return a+b>0xff;}
static inline bool CarryFrom16_add2(uint32_t a, uint32_t b) {return a+b>0xffff;}
static inline bool CarryFrom_add2(uint32_t a, uint32_t b) {return (a+b)<a;}

static inline bool CarryFrom_add3(uint32_t a, uint32_t b, uint32_t c) {
  return CarryFrom_add2(a,b) || CarryFrom_add2(a+b,c);
}

static inline bool OverflowFrom_add2(uint32_t a, uint32_t b) {
  const uint32_t r = a+b;
  return ((a^~b)&(a^r))>>31;
}

static inline bool OverflowFrom_add3(uint32_t a, uint32_t b, bool unused) {
  return OverflowFrom_add2(a,b);
}

static inline bool BorrowFrom_sub2(uint32_t a, uint32_t b) {return a<b;}

static inline bool BorrowFrom_sub3(uint32_t a, uint32_t b, uint32_t c) {
  return BorrowFrom_sub2(a,b) || BorrowFrom_sub2(a-b,c);
}

static inline bool OverflowFrom_sub2(uint32_t a, uint32_t b) {
  const uint32_t r = a-b;
  return ((a^b)&(a^r))>>31;
}

static inline bool OverflowFrom_sub3(uint32_t a, uint32_t b, bool unused) {
  return OverflowFrom_sub2(a,b);
}

static inline uint32_t rotate_right(uint32_t x, uint32_t n) {
  if (n==0) return x;
  assert(0<n && n<32 && "not implemented for this value of n");
  assert(n!=32);
  return (x<<(32-n)) | (x>>n);
}

static inline uint32_t asr(uint32_t x, uint32_t n) {
  assert(32>n && "not implemented for n>=32");
  return ((int32_t)x)>>n;
}

static uint32_t NOT(bool x) {return !x;}

/* from 24 to 30 */
static inline uint32_t SignExtend_30(uint32_t x) {return x&(1<<23) ? 0x7f000000|x : x;}

/* from 16 to 32 */
static inline uint32_t SignExtend16(uint32_t x) {return x&(1<<15) ? 0xffff0000|x : x;}

/* from 8 to 32 */
static inline uint32_t SignExtend8(uint32_t x) {return x&(1<<7) ? 0xffffff00|x : x;}

static inline uint32_t ZeroExtend(uint32_t x) {return x;}

static inline uint32_t get_bits(uint32_t x, size_t a, size_t b) {
  /* return x[a:b] */
  assert(32>a && a>b && a-b+1 < 32);
  return (x>>b) & ((1lu<<(a-b+1))-1);
}

static inline uint32_t get_bits64(uint64 x, size_t a, size_t b) {
  /* return x[a:b] */
  assert(64>a && a>b && a-b+1 <= 32);
  return I64_to_int32(I64_and(I64_lsr(x, b), I64_sub(I64_lsl(I64_of_int32(1),a-b+1), I64_of_int32(1))));
}

static inline bool get_bit(uint32_t x, uint32_t n) { /* return x[a] */
  return (x>>n)&1;
}

static inline void set_bit(uint32_t *dst, uint32_t num, bool src) {
  if (src) *dst |= (1<<num);
  else *dst &=~ (1<<num);
}

extern void set_field(uint32_t *dst, uint32_t a, uint32_t b, uint32_t src);
/* dst[a:b] = src, with a>b */

/* UnsignedSat is never used with n = 32 */
extern uint32_t SignedSat32_add(int32_t a, int32_t b);
extern uint32_t SignedSat32_sub(int32_t a, int32_t b);
extern uint32_t SignedSat32_double(int32_t a);
extern bool SignedDoesSat32_add(int32_t a, int32_t b);
extern bool SignedDoesSat32_sub(int32_t a, int32_t b);
extern bool SignedDoesSat32_double(int32_t a);
extern uint32_t SignedSat(int64 a, uint32_t b);
extern uint32_t SignedDoesSat(int64 a, uint32_t b);
extern uint32_t UnsignedSat(int32_t a, uint32_t b);
extern uint32_t UnsignedDoesSat(int32_t a, uint32_t b);

END_SIMSOC_NAMESPACE

#endif /* ARM_MATH_H */
