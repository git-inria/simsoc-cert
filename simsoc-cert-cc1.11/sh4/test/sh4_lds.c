int main() {
  asm volatile ("mov #0x78, r0\n\t"
                "lds r0, pr\n\t"
                "lds.l @r15+, macl\n\t");
}

