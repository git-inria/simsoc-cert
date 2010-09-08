#include "arm_iss.h"
#include "arm_processor.h"
#include "common.h"
#include "elf_loader.h"
#include <string.h>

using namespace std;

class MyElfFile : public ElfFile {
  MMU *mmu;
public:
  MyElfFile(const char* elf_file, MMU *mmu_): ElfFile(elf_file), mmu(mmu_) {}

  void write_to_memory(const char *data, size_t start, size_t size) {
    for (uint32_t j = 0; j<size; ++j)
      write_byte(mmu,start+j,data[j]);
  }
};

void test_decode(Processor *proc, MyElfFile &elf) {
  uint32_t a = elf.get_text_start();
  const uint32_t ea = a + elf.get_text_size();
  assert((a&3)==0 && (ea&3)==0 && "address misaligned");
  for (; a!=ea; a+=4) {
    sl_debug = false;
    const uint32_t bincode = read_word(&proc->mmu,a);
    sl_debug = true;
    DEBUG(<<"decode: " <<hex);
    DEBUG(.width(10));
    DEBUG(<<bincode <<" -> ");
    bool found = decode_and_exec(proc,bincode);
    if (!found)
      DEBUG(<<"undefined or unpredictable\n");
  }
}

/* we stop the simulation when we recognize this instruction */
const uint32_t infinite_loop = 0xea000000 | (-2 & 0x00ffffff); /* = B #-2*4 */

void simulate(Processor *proc, MyElfFile &elf) {
  uint32_t inst_count = 0;
  uint32_t bincode;
  const uint32_t entry = elf.get_initial_pc();
  INFO(<<"entry point: " <<hex <<entry <<'\n');
  set_pc(proc,entry);
  proc->jump = false;
  do {
    DEBUG(<<"---------------------\n");
    bincode = read_word(&proc->mmu,address_of_current_instruction(proc));
    bool found = decode_and_exec(proc,bincode);
    if (!found)
      TODO("Unpredictable or undefined instruction");
    if (proc->jump)
      proc->jump = false;
    else
      *proc->pc += 4;
    ++inst_count;
  } while (bincode!=infinite_loop);
  DEBUG(<<"---------------------\n");
  INFO(<<"Reached infinite loop after " <<dec <<inst_count
       <<" instructions executed.\n");
}

void usage(const char *pname) {
  cout <<"Simple ARMv6 simulator.\n"
       <<"Usage: " <<pname <<" <options> <elf_file>\n"
       <<"\t-d    turn off debugging information\n"
       <<"\t-i    turn off normal information\n"
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
  Processor proc;
  init_Processor(&proc);
  MyElfFile elf(filename, &proc.mmu);
  { const bool tmp = sl_debug;
    sl_debug = false;
    elf.load_sections();
    sl_debug = tmp;}
  if (sl_exec)
    simulate(&proc,elf);
  else
    test_decode(&proc,elf);
  if (show_r0)
    cout <<"r0 = " <<dec <<reg(&proc,0) <<endl;
  if (check_r0 && reg(&proc,0)!=expected_r0) {
    cout <<"Error: r0 contains " <<(hexa_r0? hex : dec) <<reg(&proc,0)
         <<" instead of " <<expected_r0 <<".\n";
    destruct_Processor(&proc);
    return 4;
  }
  destruct_Processor(&proc);
  return 0;
}
