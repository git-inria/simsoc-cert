/*
SimSoC-Cert, a toolkit for generating certified processor simulators
See the COPYRIGHTS and LICENSE files
 */

/* After 740 instructions executed, r0 should contain 1+2+...+42=903 */

#include "common.h"

const uint32_t N = 42;

int sum(int n) {
  if (n<=0) return 0;
  else return sum(n-1)+n;
}

int main() {
  return sum(N);
}
