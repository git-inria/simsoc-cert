#include "arm_iss.hpp"
#include <elf_loader.hpp>

class MyElfFile : public ElfFile {
  ARM_MMU *mmu;
public:
  MyElfFile(const char* elf_file, ARM_MMU *mmu_): ElfFile(elf_file), mmu(mmu_) {}

  void write_to_memory(const char *data, size_t start, size_t size) {
    for (uint32_t j = 0; j<size; ++j)
      mmu->write_byte(start+j,data[j]);
  }
};

int main(int argc, const char *argv[]) {
  if (argc!=2)
    ERROR("ELF file missing or wrong number of arguments");
  const char *filename = argv[1];
  ARM_ISS iss;
  MyElfFile elf(filename, &iss.proc.mmu);
  elf.load_sections();
  uint32_t a = elf.get_text_start();
  const uint32_t ea = a + elf.get_text_size();
  assert((a&3)==0 && (ea&3)==0 && "address misaligned");
  for (; a!=ea; a+=4) {
    const uint32_t bincode = iss.proc.mmu.read_word(a);
    std::cerr <<"decode: " <<std::hex;
    std::cerr.width(8);
    std::cerr <<bincode <<" ->";
    std::cerr.width(0);
    bool found = iss.decode_and_exec(bincode);
    if (!found)
      std::cerr <<" undefined or unpredicatable";
    std::cerr <<std::endl;
  }
  return 0;
}
