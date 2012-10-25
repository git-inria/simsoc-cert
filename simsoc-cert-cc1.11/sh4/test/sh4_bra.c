int main() {
  asm volatile ("mov #1, r0\n\t"
                "mov #2, r1\n\t"
                "bra trget\n\t"
                "add r0, r1\n\t"
                "trget:\n\t");
}

