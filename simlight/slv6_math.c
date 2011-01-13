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
  uint32_t count = 0;
  while (x) {
    count += x&1;
    x >>= 1;
  }
  return count;
}

void set_field(uint32_t *dst, uint32_t a, uint32_t b, uint32_t src) {
  assert(a>b);
  const uint32_t mask = ((1<<(a-b+1))-1)<<b;
  *dst &= ~mask;
  *dst |= (src<<b)&mask;
}

uint32_t SignedSat32_add(int32_t a, int32_t b) {
  return SignedSat((int64_t)a + (int64_t)b,32);
}

uint32_t SignedSat32_sub(int32_t a, int32_t b) {
  return SignedSat((int64_t)a - (int64_t)b,32);
}

uint32_t SignedSat32_double(int32_t a) {
  return SignedSat(2*(int64_t)a,32);
}

bool SignedDoesSat32_add(int32_t a, int32_t b) {
  return SignedDoesSat((int64_t)a + (int64_t)b,32);
}

bool SignedDoesSat32_sub(int32_t a, int32_t b) {
  return SignedDoesSat((int64_t)a - (int64_t)b,32);
}

bool SignedDoesSat32_double(int32_t a) {
  return SignedDoesSat(2*(int64_t)a,32);
}

uint32_t SignedSat(int64_t x, uint32_t n) {
  if (x < -(1<<(n-1))) return -(1<<(n-1));
  if (x > (1<<(n-1))-1) return (1<<(n-1))-1;
  return x;
}

uint32_t SignedDoesSat(int64_t x, uint32_t n) {
  return x < -(1<<(n-1)) || x > (1<<(n-1))-1;
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
