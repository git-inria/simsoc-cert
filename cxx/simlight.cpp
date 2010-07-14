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
    sl_debug = false;
    const uint32_t bincode = iss.proc.mmu.read_word(a);
    sl_debug = true;
    DEBUG(<<"decode: " <<hex);
    DEBUG(.width(8));
    DEBUG(<<bincode <<" -> ");
    bool found = iss.decode_and_exec(bincode);
    if (!found)
      DEBUG(<<" undefined or unpredictable");
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

void usage(const char *pname) {
  cout <<"Simple ARMv6 simulator.\n"
       <<"Usage: " <<pname <<" [-d] [-e] <elf_file>\n"
       <<"\t-d   turn of debugging information\n"
       <<"\t-i   turn of normal information\n"
       <<"\t-dec decode the .text section (turn off simulation)\n";
}

int main(int argc, const char *argv[]) {
  const char *filename = NULL;
  for (int i = 1; i<argc; ++i) {
    if (argv[i][0]=='-') {
      if (!strcmp(argv[i],"-d"))
        sl_debug = false;
      else if (!strcmp(argv[i],"-i"))
        sl_info = false;
      else if (!strcmp(argv[i],"-dec"))
        sl_exec = false;
      else {
        cout <<"Error: unrecognized option: \"" <<argv[i] <<"\".\n\n";
        usage(argv[0]);
        return 1;
      }
    } else {
      if (filename) {
        cout <<"Error: two elf files: \"" <<filename <<"\" and \""
             <<argv[i] <<"\".\n\n";
        usage(argv[0]);
        return 1;
      }
      filename = argv[i];
    }
  }
  if (!filename) {
    if (argc>1)
      cout <<"Error: no elf file.\n\n";
    usage(argv[0]);
    return (argc>1);
  }
  ARM_ISS iss;
  MyElfFile elf(filename, &iss.proc.mmu);
  { const bool tmp = sl_debug;
    sl_debug = false;
    elf.load_sections();
    sl_debug = true;}
  if (sl_exec)
    simulate(iss,elf);
  else
    test_decode(iss,elf);
  return 0;
}
