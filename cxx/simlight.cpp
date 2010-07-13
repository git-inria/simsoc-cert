#include "arm_iss.hpp"
#include "common.hpp"
#include <elf_loader.hpp>

using namespace std;

class MyElfFile : public ElfFile {
  ARM_MMU *mmu;
public:
  MyElfFile(const char* elf_file, ARM_MMU *mmu_): ElfFile(elf_file), mmu(mmu_) {}

  void write_to_memory(const char *data, size_t start, size_t size) {
    for (uint32_t j = 0; j<size; ++j)
      mmu->write_byte(start+j,data[j]);
  }
};

void test_decode(ARM_ISS &iss, MyElfFile &elf) {
  uint32_t a = elf.get_text_start();
  const uint32_t ea = a + elf.get_text_size();
  assert((a&3)==0 && (ea&3)==0 && "address misaligned");
  for (; a!=ea; a+=4) {
    const uint32_t bincode = iss.proc.mmu.read_word(a);
    DEBUG(<<"decode: " <<hex);
    DEBUG(.width(8));
    DEBUG(<<bincode <<" ->");
    bool found = iss.decode_and_exec(bincode);
    if (!found)
      DEBUG(<<" undefined or unpredictable");
    DEBUG(<<endl);
  }
}

// we stop the simulation when we recongnize this instruction
const uint32_t infinite_loop = 0xea000000 | (-2 & 0x00ffffff); // = B #-2*4

void simulate(ARM_ISS &iss, MyElfFile &elf) {
  uint32_t inst_count = 0;
  uint32_t bincode;
  const uint32_t entry = elf.get_start_address();
  INFO(<<"entry point: " <<hex <<entry <<'\n');
  iss.proc.set_pc(entry);
  iss.proc.jump = false;
  do {
    DEBUG(<<"---------------------\n");
    bincode = iss.proc.mmu.read_word(iss.proc.pc-8);
    bool found = iss.decode_and_exec(bincode);
    if (!found)
      TODO("Unpredictable or undefined instruction");
    if (iss.proc.jump)
      iss.proc.jump = false;
    else
      iss.proc.pc += 4;
    ++inst_count;
  } while (bincode!=infinite_loop);
  DEBUG(<<"---------------------\n");
  INFO(<<"Reached infinite loop after " <<dec <<inst_count
       <<" instructions executed.\n");
  INFO(<<"r0 = " <<dec <<iss.proc.reg(0) <<endl);
}

int main(int argc, const char *argv[]) {
  if (argc!=2)
    ERROR("ELF file missing or wrong number of arguments");
  const char *filename = argv[1];
  ARM_ISS iss;
  MyElfFile elf(filename, &iss.proc.mmu);
  elf.load_sections();
  simulate(iss,elf);
  return 0;
}
