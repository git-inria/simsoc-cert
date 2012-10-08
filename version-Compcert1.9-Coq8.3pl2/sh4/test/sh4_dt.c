int main() {
  asm volatile ("mov #4, r5\n\t"
                "loop:\n\t"
                "add r0, r1\n\t"
                "dt r5\n\t"
                "bf loop\n\t");
}

