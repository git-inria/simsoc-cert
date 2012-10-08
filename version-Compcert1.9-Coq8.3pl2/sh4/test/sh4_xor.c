int main() {
  asm volatile ("mov #0x55, r0\n\t"
                "mov #0xaa, r1\n\t"
                "xor r0, r1\n\t"
                "xor #0xf0, r0\n\t");
}

