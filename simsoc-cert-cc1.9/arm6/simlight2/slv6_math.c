/* SimSoC-Cert, a library on processor architectures for embedded systems. */
/* See the COPYRIGHTS and LICENSE files. */

/* Arithmetic and logic functions. */

#include "slv6_math.h"

BEGIN_SIMSOC_NAMESPACE

uint32_t bit_position_of_most_significant_1(uint32_t x) {
  int32_t n;
  for (n = 31; n>=0; --n)
    if (x&(1<<n))
      return n;
  assert(false && "x is zero");
  return ~0;
}

uint32_t Number_Of_Set_Bits_In(uint32_t x) {
  /* source:
   * http://stackoverflow.com/questions/109023/best-algorithm-to-count-the-number-of-set-bits-in-a-32-bit-integer
   * I have tested it for all values between 0 and 2^16-1
   */
  x = x - ((x >> 1) & 0x55555555);
  x = (x & 0x33333333) + ((x >> 2) & 0x33333333);
  return (((x + (x >> 4)) & 0xF0F0F0F) * 0x1010101) >> 24;
}

#if 0 /* the old slow implementation, which can be used as reference */
uint32_t Number_Of_Set_Bits_In(uint32_t x) {
  uint32_t count = 0;
  while (x) {
    count += x&1;
    x >>= 1;
  }
  return count;
}
#endif

void set_field(uint32_t *dst, uint32_t a, uint32_t b, uint32_t src) {
  assert(a>b);
  if (a-b+1==32) {
    *dst = src;
    return;
  }
  const uint32_t mask = ((1<<(a-b+1))-1)<<b;
  *dst &= ~mask;
  *dst |= (src<<b)&mask;
}

uint32_t SignedSat32_add(int32_t a, int32_t b) {
  return SignedSat(I64_add(I64_of_int32(a), I64_of_int32(b)),32);
}

uint32_t SignedSat32_sub(int32_t a, int32_t b) {
  return SignedSat(I64_sub(I64_of_int32(a), I64_of_int32(b)),32);
}

uint32_t SignedSat32_double(int32_t a) {
  return SignedSat(I64_mul(I64_of_int32(2), I64_of_int32(a)),32);
}

bool SignedDoesSat32_add(int32_t a, int32_t b) {
  return SignedDoesSat(I64_add(I64_of_int32(a), I64_of_int32(b)),32);
}

bool SignedDoesSat32_sub(int32_t a, int32_t b) {
  return SignedDoesSat(I64_sub(I64_of_int32(a), I64_of_int32(b)),32);
}

bool SignedDoesSat32_double(int32_t a) {
  return SignedDoesSat(I64_mul(I64_of_int32(2), I64_of_int32(a)),32);
}

uint32_t SignedSat(int64 x, uint32_t n) {
  if (I64_compare(x, I64_neg(I64_lsl(I64_of_int32(1), n-1))) == -1) return -(1<<(n-1));
  if (I64_compare(x, I64_sub(I64_lsl(I64_of_int32(1), n-1), 
                             I64_of_int32(1))) == 1) return (1<<(n-1))-1;
  return I64_to_int32(x);
}

uint32_t SignedDoesSat(int64 x, uint32_t n) {
  return I64_compare(x, I64_neg(I64_lsl(I64_of_int32(1), n-1))) == -1 
    || I64_compare(x, I64_sub(I64_lsl(I64_of_int32(1), n-1), I64_of_int32(1))) == 1;
}

uint32_t UnsignedSat(int32_t x, uint32_t n) {
  assert(n<32);
  if (x < 0) return 0;
  if (x > (1<<n)-1) return (1<<n)-1;
  return x;
}

uint32_t UnsignedDoesSat(int32_t x, uint32_t n) {
  assert(n<32);
  return x < 0 || x > (1<<n)-1;
}

END_SIMSOC_NAMESPACE
