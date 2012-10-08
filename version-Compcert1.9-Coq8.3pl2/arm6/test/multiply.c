/* Derived from SimSoC, Copyright © INRIA 2007, 2008, 2009, 2010
 * LGPL license version 3 */

/* test some multiplication instructions (no assembly)
 * After 130 instructions executed, r0 should contain 0xf = 15 */

#include "common.h"

int count = 0;

#define CHECK(ID, RESULT, EXPECTED)             \
  if ((RESULT)==(EXPECTED)) count+=(ID);

int main()
{
  {
    int a1=-8,b1=6;
    long c1;
    c1=a1*b1;
    CHECK(1,c1,-48);
  }{
    unsigned int a2=8,b2=6;
    long c2;
    c2=a2*b2;
    CHECK(2,c2,48);
  }{
    long long int a3=-80000,b3=60000;
    long long int c3;
    c3=a3*b3;
    CHECK(4,c3,-4800000000LL);
  }{
    unsigned long long int a4=80000,b4=60000;
    unsigned long long int c4;
    c4=a4*b4;
    CHECK(8,c4,4800000000ULL);
  }
  return count;
}
