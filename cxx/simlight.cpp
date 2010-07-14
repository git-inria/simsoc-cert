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
    DEBUG(.width(10));
    DEBUG(<<bincode <<" -> ");
    bool found = iss.decode_and_exec(bincode);
    if (!found)
      DEBUG(<<"undefined or unpredictable\n");
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
}

void usage(const char *pname) {
  cout <<"Simple ARMv6 simulator.\n"
       <<"Usage: " <<pname <<" <options> <elf_file>\n"
       <<"\t-d    turn of debugging information\n"
       <<"\t-i    turn of normal information\n"
       <<"\t-r0   display the content of r0 before exiting\n"
       <<"\t-r0=N exit with an error status if r0!=N at the end of simulation\n"
       <<"\t-dec  decode the .text section (turn off simulation)\n";
}

int main(int argc, const char *argv[]) {
  cout <<showbase;
  const char *filename = NULL;
  bool show_r0 = false;
  bool check_r0 = false;
  bool hexa_r0 = false;
  uint32_t expected_r0 = 0;
  for (int i = 1; i<argc; ++i) {
    if (argv[i][0]=='-') {
      if (!strcmp(argv[i],"-d"))
        sl_debug = false;
      else if (!strcmp(argv[i],"-i"))
        sl_info = false;
      else if (!strcmp(argv[i],"-r0"))
        show_r0 = true;
      else if (!strncmp(argv[i],"-r0=",4)) {
        check_r0 = true;
        expected_r0 = strtoul(argv[i]+4,NULL,0);
        hexa_r0 = !strncmp(argv[i]+4,"0x",2);
      } else if (!strcmp(argv[i],"-dec"))
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
    sl_debug = tmp;}
  if (sl_exec)
    simulate(iss,elf);
  else
    test_decode(iss,elf);
  if (show_r0)
    cout <<"r0 = " <<dec <<iss.proc.reg(0) <<endl;
  if (check_r0 && iss.proc.reg(0)!=expected_r0) {
    cout <<"Error: r0 contains " <<(hexa_r0? hex : dec) <<iss.proc.reg(0)
         <<" instead of " <<expected_r0 <<".\n";
    return 4;
  }
  return 0;
}
