int main() {
  asm volatile("mov #0xa, r0\n\t"
               "mov #0x5, r1\n\t"
               "and r0, r1\n\t"
               "and #0xf, r0\n\t"
               "and.b #0x80, @(r0, gbr)\n\t");
}

