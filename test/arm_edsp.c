/* test the EDSP instructions
 * After ? instructions executed, r0 should contain 0x7fffff = 8,388,607 */

#include "common.h"

int count = 0;

#define CHECK(OP, TEST) \
  if ((TEST)) count+=(OP);

#define QFLAG(X) ((X >> 27) & 0x1)

/* ------------------------------------------------------------------ */
void test_QADD(void) {
  uint32_t x, f;

  asm("msr  CPSR_f, #0 \t\n"
      "qadd %0, %2, %3 \t\n"
      "mrs  %1, CPSR   \r\n"
      : "=&r" (x), "=r" (f)
      : "r" (0x80005c7a), "r" (0x24bc75e1));

  CHECK(1, (x == 0xa4bcd25b) && !QFLAG(f));
}

void test_QADD_Q(void) {
  uint32_t x, f;

  asm("msr  CPSR_f, #0 \t\n"
      "qadd %0, %2, %3 \t\n"
      "mrs  %1, CPSR   \r\n"
      : "=&r" (x), "=r" (f)
      : "r" (0x7fffa386), "r" (0x24bc75e1));

  CHECK(2, (x == 0x7fffffff) && QFLAG(f));
}

void test_QDADD(void) {
  uint32_t x, f;

  asm("msr   CPSR_f, #0 \t\n"
      "qdadd %0, %2, %3 \t\n"
      "mrs   %1, CPSR   \r\n"
      : "=&r" (x), "=r" (f)
      : "r" (0xc0002e3d), "r" (0x24bc75e1));

  CHECK(4, (x == 0x97919ff) && !QFLAG(f));
}

/* ------------------------------------------------------------------ */
void test_QSUB(void) {
  uint32_t x, f;

  asm("msr  CPSR_f, #0 \t\n"
      "qsub %0, %2, %3 \t\n"
      "mrs  %1, CPSR   \r\n"
      : "=&r" (x), "=r" (f)
      : "r" (0x7fffa386), "r" (0x24bc75e1));

  CHECK(8, (x == 0x5b432da5) && !QFLAG(f));
}

void test_QSUB_Q(void) {
  uint32_t x, f;

  asm("msr  CPSR_f, #0 \t\n"
      "qsub %0, %2, %3 \t\n"
      "mrs  %1, CPSR   \r\n"
      : "=&r" (x), "=r" (f)
      : "r" (0x80005c7a), "r" (0x24bc75e1));

  CHECK(16, (x == 0x80000000) && QFLAG(f));
}

/* ------------------------------------------------------------------ */
void test_SMLA_BB(void) {
  uint32_t x;

  asm("smlabb %0, %1, %2, %3"
      : "=&r" (x)
      : "r"   (0xffff1234),
        "r"   (0xffffece2),
        "r"   (0x00345678));

  CHECK(32, (x == 0xfed85860));
}

void test_SMLA_BB_Q(void) {
  uint32_t x, f;

  asm("msr    CPSR_f, #0     \r\n"
      "smlabb %0, %2, %3, %4 \r\n"
      "mrs    %1, CPSR       \r\n"
      : "=&r" (x), "=r" (f)
      : "r"   (0xffff1234),
        "r"   (0xffffece2),
        "r"   (0x812bfe18));

  CHECK(64, (x == 0x7fd00000) && QFLAG(f));
}

void test_SMLA_BT(void) {
  uint32_t x;

  asm("smlabt %0, %1, %2, %3"
      : "=&r" (x)
      : "r"   (0xffff1234),
        "r"   (0xece2ffff),
        "r"   (0x00345678));

  CHECK(128, (x == 0xfed85860));
}

void test_SMLA_TB(void) {
  uint32_t x;

  asm("smlatb %0, %1, %2, %3"
      : "=&r" (x)
      : "r"   (0x1234ffff),
        "r"   (0xffffece2),
        "r"   (0x00345678));

  CHECK(256, (x == 0xfed85860));
}

void test_SMLA_TT(void) {
  uint32_t x;

  asm("smlatt %0, %1, %2, %3"
      : "=&r" (x)
      : "r"   (0x1234ffff),
        "r"   (0xece2ffff),
        "r"   (0x00345678));

  CHECK(512, (x == 0xfed85860));
}


/* ------------------------------------------------------------------ */
void test_SMLAW_B(void) {
  uint32_t x, f;

  asm("msr    CPSR_f, #0     \r\n"
      "smlawb %0, %2, %3, %4 \r\n"
      "mrs    %1, CPSR       \r\n"
      : "=&r" (x), "=r" (f)
      : "r"   (0x12345678),
        "r"   (0xffffece2),
        "r"   (0x815c048e));

  CHECK(1024, (x == 0x80000000) && !QFLAG(f));
}

void test_SMLAW_B_Q(void) {
  uint32_t x, f;

  asm("msr    CPSR_f, #0     \r\n"
      "smlawb %0, %2, %3, %4 \r\n"
      "mrs    %1, CPSR       \r\n"
      : "=&r" (x), "=r" (f)
      : "r"   (0x12345678),
        "r"   (0xffffece2),
        "r"   (0x815c048d));

  CHECK(2048, (x == 0x7fffffff) && QFLAG(f));
}

void test_SMLAW_T(void) {
  uint32_t x;

  asm("smlawt %0, %1, %2, %3"
      : "=&r" (x)
      : "r"   (0x12345678),
        "r"   (0xece2ffff),
        "r"   (0x00345678));

  CHECK(0x1000, (x == 0xfed851ea));
}

/* ------------------------------------------------------------------ */
void test_SMULBB(void) {
  uint32_t x;

  asm("smulbb %0, %1, %2"
      : "=&r" (x)
      : "r"   (0xffff1234), "r" (0xffffece2));

  CHECK(0x2000, (x == 0xfea401e8));
}

void test_SMULBT(void) {
  uint32_t x;

  asm("smulbt %0, %1, %2"
      : "=&r" (x)
      : "r"   (0xffff1234), "r" (0xece2ffff));

  CHECK(0x4000, (x == 0xfea401e8));
}

void test_SMULTB(void) {
  uint32_t x;

  asm("smultb %0, %1, %2"
      : "=&r" (x)
      : "r"   (0x1234ffff), "r" (0xffffece2));

  CHECK(0x8000, (x == 0xfea401e8));
}

void test_SMULTT(void) {
  uint32_t x;

  asm("smultt %0, %1, %2"
      : "=&r" (x)
      : "r"   (0x1234ffff), "r" (0xece2ffff));

  CHECK(0x10000, (x == 0xfea401e8));
}

/* ------------------------------------------------------------------ */
void test_SMULW_B(void) {
  uint32_t x;

  asm("smulwb %0, %1, %2"
      : "=&r" (x)
      : "r"   (0x12345678),
        "r"   (0xffffece2));

  CHECK(0x20000, (x == 0xfea3fb72));
}

void test_SMULW_T(void) {
  uint32_t x;

  asm("smulwt %0, %1, %2"
      : "=&r" (x)
      : "r"   (0x12345678),
        "r"   (0xece2ffff));

  CHECK(0x40000, (x == 0xfea3fb72));
}

/* ------------------------------------------------------------------ */
void test_SMLAL_BB(void) {
  uint32_t xlo, xhi;

  xlo = 0x00034567;
  xhi = 0x36efa293;

  asm("smlalbb %0, %1, %2, %3"
      : "+&r" (xlo), "+&r" (xhi)
      : "r"   (0xffff1234),
        "r"   (0xffffece2));

  CHECK(0x80000, (xlo == 0xfea7474f) && (xhi == 0x36efa292));
}

void test_SMLAL_BT(void) {
  uint32_t xlo, xhi;

  xlo = 0x00034567;
  xhi = 0x36efa293;

  asm("smlalbt %0, %1, %2, %3"
      : "+&r" (xlo), "+&r" (xhi)
      : "r"   (0xffff1234),
        "r"   (0xece2ffff));

  CHECK(0x100000, (xlo == 0xfea7474f) && (xhi == 0x36efa292));
}

void test_SMLAL_TB(void) {
  uint32_t xlo, xhi;

  xlo = 0x00034567;
  xhi = 0x36efa293;

  asm("smlaltb %0, %1, %2, %3"
      : "+&r" (xlo), "+&r" (xhi)
      : "r"   (0x1234ffff),
        "r"   (0xffffece2));

  CHECK(0x200000, (xlo == 0xfea7474f) && (xhi == 0x36efa292));
}

void test_SMLAL_TT(void) {
  uint32_t xlo, xhi;

  xlo = 0x00034567;
  xhi = 0x36efa293;

  asm("smlaltt %0, %1, %2, %3"
      : "+&r" (xlo), "+&r" (xhi)
      : "r"   (0x1234ffff),
        "r"   (0xece2ffff));

  CHECK(0x400000, (xlo == 0xfea7474f) && (xhi == 0x36efa292));
}

/* ------------------------------------------------------------------ */
int main(void) {
  test_QADD();
  test_QADD_Q();
  test_QDADD();
  test_QSUB();
  test_QSUB_Q();
  test_SMLA_BB();
  test_SMLA_BB_Q();
  test_SMLA_BT();
  test_SMLA_TB();
  test_SMLA_TT();
  test_SMLAW_B();
  test_SMLAW_B_Q();
  test_SMLAW_T();
  test_SMULBB();
  test_SMULBT();
  test_SMULTB();
  test_SMULTT();
  test_SMULW_B();
  test_SMULW_T();
  test_SMLAL_BB();
  test_SMLAL_BT();
  test_SMLAL_TB();
  test_SMLAL_TT();
  return count;
}
