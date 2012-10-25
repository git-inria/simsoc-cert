/* Derived from SimSoC, Copyright © INRIA 2007, 2008, 2009, 2010
 * LGPL license version 3 */

/* test various instructions (no assembly)
 * After 190,505 instructions executed, r0 should contain 0xff = 255 */

#include "common.h"

/* used by hello_test, not related to count variable of other tests */
int counter = 0;

void increment() {
  ++counter;
}

int hello_test() {
  int		i,j;
  int		a0[100];
  long int 	a1[100];
  unsigned int	a3[100];
  for (i = 0; i<100; i++) {
    a0[i] = i-50;
    a1[i] = i*100;
    a3[i] = i+50;
  }
  for (j = 0; j<a1[2]; j += 50) {
    /* print_str("Hello world\n"); */
    increment();
  }
  if (counter==4) {
    /* print_str("Hello test OK!\n"); */
    return 1;
  } else {
    /* print_str("Hello test fail!\n"); */
    return 0;
  }
}

int comparison_test(void)
{
  int a,b,c,d;
  a=0;b=1;c=1;d=100;
  if(a < b){
    if(a <= b){
      if(b == c){
        if(d > c){
          if(c >=b){
            if(a != d){
              /* print_str("comparison OK!\n"); */
              return 1;
            }
          }
        }
      }
    }
  }
  /* print_str("comparison fail!\n"); */
  return 0;
}

int bit_shift_test(char object, char target, char method)
{
  char tmp = 0;
  switch(method) {
  case 0: tmp = object<<1; break;
  case 1: tmp = object<<2; break;
  case 2: tmp = object<<3; break;
  case 3: tmp = object<<4; break;
  case 4: tmp = object>>1; break;
  case 5: tmp = object>>2; break;
  case 6: tmp = object>>3; break;
  case 7: tmp = object>>4; break;
  default:
    tmp = !target;
    break;
  }
  if (tmp==target)
    return 1;
  else
    return 0;
}

int bit_and_test(char and1, char and2, char target)
{
  char tmp = and1&and2;
  if (tmp==target)
    return 1;
  else
    return 0;
}

int bit_or_test(char or1, char or2, char target)
{
  char tmp= or1 | or2;
  if(tmp == target)
    return 1;
  else
    return 0;
}

int bit_not_test(char not, char target)
{
  char tmp = ~not;
  if (tmp==target)
    return 1;
  else
    return 0;
}

int bit_xor_test(char xor1, char xor2, char target)
{
  char tmp = xor1^xor2;
  if (tmp==target)
    return 1;
  else
    return 0;
}

int bit_test(void)
{
  unsigned char i;
  char j;

  /* shift test */
  for (i = 15; i>0; i--) {
    j = i*16;
    if (bit_shift_test(i,j,3)==0)
      break;
  }
  if (i!=0) {
    /* print_str("bit_shift fail!\n"); */
    return 0;
  } /* else */
    /* print_str("bit_shift OK!\n"); */

  /* and test */
  j = 15;
  for (i = 15; i>0; i--) {
    if (bit_and_test(i,j,(i<<4)>>4)==0)
      break;
  }
  if (i!=0) {
    /* print_str("bit_and fail!\n"); */
    return 0;
  } /* else */
    /* print_str("bit_and OK!\n"); */

  /* or test */
  j = 15;
  for (i = 15; i>0; i--) {
    if (bit_or_test(i,j,15)==0)
      break;
  }
  if (i!=0) {
    /* print_str("bit_or fail!\n"); */
    return 0;
  } /* else */
    /* print_str("bit_or OK!\n"); */

  /* not test */
  for (i = 255; i>0; i--) {
    if (bit_not_test(i,255-i)==0)
      break;
  }
  if (i!=0) {
    /* print_str("bit_not fail!\n"); */
    return 0;;
  } /* else */
    /* print_str("bit_not OK!\n"); */

  /* xor test */
  for (i=255; i>0; i--) {
    if (bit_xor_test(i,255-i,255)==0)
      break;
    if (bit_xor_test(i,i,0)==0)
      break;
  }
  if (i!=0) {
    /* print_str("bit_xor fail!\n"); */
    return 0;
  } /* else */
    /* print_str("bit_xor OK!\n"); */
  return 1;
}

int logic_test()
{
  int a,b,c,d;
  a =0 ; b = 1; c = 100; d = -100;
  if (!a&&b) {
    if (a||b) {
      /* print_str("logic test OK!\n"); */
      return 1;
    }
  }
  /* print_str("logic test fail!\n"); */
  return 0;
}

int if_test()
{
  int a,b,c,d;
  a = 1; b = 1; c = 3; d = 4;
  if (a==b) {
    if (b<=c) {
      if (d>=c) {
        /* print_str("if test OK!\n"); */
        return 1;
      }
    }
  }
  /* print_str("if test fail!\n"); */
  return 0;
}

int loop_test()
{
  int i,j;
  for (i = 0; i<1000; i++);
  if (i!=1000) {
    /* print_str("loop test fail!\n"); */
    return 0;
  }
  for (j = 0; j<10000; j++);
  if (j!=10000) {
    /* print_str("loop test fail!\n"); */
    return 0;
  }
  do {
    i--;
  } while (i>0);
  while (j>0) {
    j--;
  }
  if (i==0&&j==0) {
    /* print_str("loop test OK!\n"); */
    return 1;
  } else {
    /* print_str("loop test fail!\n"); */
    return 0;
  }
}

int recursion(int recur)
{
  int tmp = recur;
  if (recur<100) {
    recur++;
    tmp += recursion(recur);
    return tmp;
  } else
    return recur;
}

int recursion_test()
{
  if (recursion(1)==5050) {
    /* print_str("recursion test OK!\n"); */
    return 1;
  } else {
    /* print_str("recursion test fail!\n"); */
    return 0;
  }
}

int goto_test()
{
  int i = 0;
 h1:
  i++;
  if (i>10)
    goto h3;
 h2:
  if (i<20)
    i += 10;
  goto h1;
 h3:
  if (i>100) {
    /* print_str("goto_test OK!\n"); */
    return 1;
  } else {
    i*=2;
    goto h2;
  }
}

int count = 0;

#define CHECK(OP, TEST) \
  if ((TEST)) count+=(OP);

int main()
{
  CHECK(1,hello_test());
  CHECK(2,comparison_test());
  CHECK(4,logic_test());
  CHECK(8,bit_test());
  CHECK(16,if_test());
  CHECK(32,loop_test());
  CHECK(64,recursion_test());
  CHECK(128,goto_test());
  return count;
}
