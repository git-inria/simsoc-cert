int main() {
  asm volatile ("mov #0x02, r0\n\t"
                "mov #0x03, r1\n\t"
                "add r0, r1\n\t"
                "add #0x01, r2\n\t"
                "add #0xfe, r3\n\t");
}

