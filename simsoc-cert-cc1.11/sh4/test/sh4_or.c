int main() {
  asm volatile ("mov #0xa5, r0\n\t"
                "mov #0x50, r1\n\t"
                "or r0, r1\n\t"
                "or #0xf0, r0\n\t");
}

