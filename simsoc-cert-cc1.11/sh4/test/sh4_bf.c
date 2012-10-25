int main() {
  asm volatile ("trget_t:\n\t"
                "clrt\n\t"
                "bt trget_t\n\t"
                "bf trget_f\n\t"
                "nop\n\t"
                "nop\n\t"
                "trget_f:\n\t");
}

