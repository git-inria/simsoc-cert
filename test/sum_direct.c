/* Example for the Coq simulator */
/* After 18 instructions executed, r0 should contain 1+2+...+42=903 */

#include "common.h"

const uint32_t N = 42;

int main() {
  return N*(N+1)/2;
}
