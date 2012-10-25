int main() {
  asm volatile ("mov #0x34, r0\n\t"
                "mov #0x12, r1\n\t"
                "swap.b r0, r1\n\t"
                "swap.w r0, r1\n\t");
}

