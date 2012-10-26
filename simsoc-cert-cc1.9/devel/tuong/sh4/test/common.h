/*
SimSoC-Cert, a toolkit for generating certified processor simulators
See the COPYRIGHTS and LICENSE files
 */

typedef unsigned char uint8_t;
typedef unsigned short uint16_t;
typedef unsigned int uint32_t;

void _start() {
  asm volatile (""); /* initialize the stack pointer */
  main();
  while(1);
}

#ifndef NULL
#define NULL 0
#endif
