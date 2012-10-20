int main() {
  asm volatile ("mov #2, r1\n\t"
                "mov #1, r0\n\t"
                "sub r0, r1\n\t");
}

