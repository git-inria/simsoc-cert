typedef unsigned int uint32_t;

const uint32_t SP = 0xff000; // intial stack pointer

void _start() __attribute__ ((naked));
void _start() {
  asm volatile ("mov sp, %0"
                :
                : "r" (SP)); /* initialize the stack pointer */
  main();
  while(1);
}
