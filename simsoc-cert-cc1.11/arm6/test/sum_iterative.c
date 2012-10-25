/*
SimSoC-Cert, a toolkit for generating certified processor simulators
See the COPYRIGHTS and LICENSE files
 */

/* After 264 instructions executed, r0 should contain 1+2+...+42=903 */

typedef unsigned int uint32_t;

const uint32_t N = 42;

const uint32_t SP = 0xff000; // intial stack pointer

void _start() __attribute__ ((naked));
void _start() {
  asm volatile ("mov sp, %0"
                :
                : "r" (SP)); /* initialize the stack pointer */

  /* iterative sum of the numbers from 0 to N */
  unsigned int sum = 0;
  unsigned int i;
  for (i = 1; i<=N; ++i)
    sum += i;

  asm volatile ("mov r0, %0\n\t": :"r"(sum): "r0"); /* we store the result in r0 */
  while(1);
}
