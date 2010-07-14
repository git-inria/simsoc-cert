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

int get_N_flag(uint32_t cpsr) {return (cpsr>>31)&1;}
int get_Z_flag(uint32_t cpsr) {return (cpsr>>30)&1;}
int get_C_flag(uint32_t cpsr) {return (cpsr>>29)&1;}
int get_V_flag(uint32_t cpsr) {return (cpsr>>28)&1;}

