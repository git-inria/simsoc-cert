#include "slv6_iss.h"
#include "slv6_processor.h"
#include "common.h"
#include "elf_loader.h"
#include "slv6_iss_printers.h"
#include <string.h>

/* function used by the ELF loader */
static SLv6_MMU *mmu_ptr = NULL;
void elf_write_to_memory(const char *data, size_t start, size_t size) {
  assert(mmu_ptr);
  uint32_t j;
  for (j = 0; j<size; ++j)
    slv6_write_byte(mmu_ptr,start+j,data[j]);
}

void test_decode_arm(struct SLv6_Processor *proc, struct ElfFile *elf) {
  uint32_t a = ef_get_text_start(elf);
  const uint32_t ea = a + ef_get_text_size(elf);
  assert((a&3)==0 && (ea&3)==0 && "address misaligned");
  sl_debug = false;
  struct SLv6_Instruction instr;
  for (; a!=ea; a+=4) {
    const uint32_t bincode = slv6_read_word(proc->mmu_ptr,a);
    printf("decode %x -> ", bincode);
    instr.args.g0.id = ~0;
    arm_decode_and_store(&instr,bincode);
    assert(instr.args.g0.id<=SLV6_INSTRUCTION_COUNT);
/*     printf("%s: %s\n", */
/*            slv6_instruction_references[instr.args.g0.id], */
/*            slv6_instruction_names[instr.args.g0.id]); */
    slv6_print_instr(stdout, &instr); fputc('\n',stdout);
  }
}

void test_decode_thumb(struct SLv6_Processor *proc, struct ElfFile *elf) {
  uint32_t a = ef_get_text_start(elf);
  const uint32_t ea = a + ef_get_text_size(elf);
  assert((a&1)==0 && (ea&1)==0 && "address misaligned");
  sl_debug = false;
  struct SLv6_Instruction instr;
  for (; a!=ea; a+=2) {
    const uint16_t bincode = slv6_read_half(proc->mmu_ptr,a);
    printf("decode %x -> ", bincode);
    instr.args.g0.id = ~0;
    thumb_decode_and_store(&instr,bincode);
    assert(instr.args.g0.id<=SLV6_INSTRUCTION_COUNT);
    printf("%s: %s\n",
           slv6_instruction_references[instr.args.g0.id],
           slv6_instruction_names[instr.args.g0.id]);
  }
}

void test_decode(struct SLv6_Processor *proc, struct ElfFile *elf) {
  const uint32_t entry = ef_get_initial_pc(elf);
  if (entry&1)
    test_decode_thumb(proc,elf);
  else
    test_decode_arm(proc,elf);
}

/* we stop the simulation when we recognize this instruction */
const uint32_t arm_infinite_loop = 0xea000000 | (-2 & 0x00ffffff); /* = B #-2*4 */
const uint32_t thumb_infinite_loop = 0xe000 | (-2 & 0x07ff); /* = B #-2*2 */

bool done(bool T, uint32_t arm, uint16_t thumb) {
  if (T)
    return thumb==thumb_infinite_loop;
  else
    return arm==arm_infinite_loop;
}

void simulate(struct SLv6_Processor *proc, struct ElfFile *elf) {
  uint32_t inst_count = 0;
  uint32_t arm_bincode;
  uint16_t thumb_bincode;
  bool found;
  const uint32_t entry = ef_get_initial_pc(elf);
  INFO(printf("entry point: %x\n", entry));
  set_pc(proc,entry);
  proc->jump = false;
  do {
    DEBUG(puts("---------------------"));
    if (proc->cpsr.T_flag) {
      thumb_bincode = slv6_read_half(proc->mmu_ptr,address_of_current_instruction(proc));
      found = thumb_decode_and_exec(proc,thumb_bincode);
    } else {
      arm_bincode = slv6_read_word(proc->mmu_ptr,address_of_current_instruction(proc));
      found = arm_decode_and_exec(proc,arm_bincode);
    }
    if (!found)
      TODO("Unpredictable or undefined instruction");
    if (proc->jump)
      proc->jump = false;
    else
      increment_pc(proc);
    slv6_hook(proc);
    ++inst_count;
  } while (!done(proc->cpsr.T_flag,arm_bincode,thumb_bincode));
  DEBUG(puts("---------------------"));
  INFO(printf("Reached infinite loop after %d instructions executed.\n", inst_count));
}

void usage(const char *pname) {
  puts("Simple ARMv6 simulator.");
  printf("Usage: %s <options> <elf_file>\n", pname);
  puts("\t-d    turn off debugging information");
  puts("\t-i    turn off normal information");
  puts("\t-r0   display the content of r0 before exiting");
  puts("\t-r0=N exit with an error status if r0!=N at the end of simulation");
  puts("\t-dec  decode the .text section (turn off simulation)");
}

int main(int argc, const char *argv[]) {
  const char *filename = NULL;
  bool show_r0 = false;
  bool check_r0 = false;
  bool hexa_r0 = false;
  uint32_t expected_r0 = 0;
  /* commmand line parsing */
  int i;
  for (i = 1; i<argc; ++i) {
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
        printf("Error: unrecognized option: \"%s\".\n\n", argv[i]);
        usage(argv[0]);
        return 1;
      }
    } else {
      if (filename) {
        printf("Error: two elf files: \"%s\" and \"%s\".\n\n",filename,argv[i]);
        usage(argv[0]);
        return 1;
      }
      filename = argv[i];
    }
  }
  if (!filename) {
    if (argc>1)
      puts("Error: no elf file.\n");
    usage(argv[0]);
    return (argc>1);
  }
  /* create the processor and the MMU */
  struct SLv6_Processor proc;
  SLv6_MMU mmu;
  SLv6_SystemCoproc cp15;
  init_MMU(&mmu, 4 /* memory start */, 0x100000 /* memory size */);
  init_CP15(&cp15);
  mmu_ptr = &mmu;
  init_Processor(&proc,&mmu,&cp15);
  /* load the ELF file */
  struct ElfFile elf;
  ef_init_ElfFile(&elf,filename);
  { const bool tmp = sl_debug;
    sl_debug = false;
    ef_load_sections(&elf);
    sl_debug = tmp;}
  /* main task */
  if (sl_exec)
    simulate(&proc,&elf);
  else
    test_decode(&proc,&elf);
  /* check result */
  if (show_r0)
    printf("r0 = %d\n",reg(&proc,0));
  if (check_r0 && reg(&proc,0)!=expected_r0) {
    if (hexa_r0)
      printf("Error: r0 contains %x instead of %x.\n",reg(&proc,0),expected_r0);
    else
      printf("Error: r0 contains %d instead of %d.\n",reg(&proc,0),expected_r0);
    destruct_Processor(&proc);
    ef_destruct_ElfFile(&elf);
    return 4;
  }
  ef_destruct_ElfFile(&elf);
  destruct_Processor(&proc);
  return 0;
}
