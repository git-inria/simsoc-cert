#include "elf.h"
#include <errno.h>
#include <fstream>
#include <iostream>
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>
#include <cstring>
#include <cstdlib>

using namespace std;

const int strn_size = 1+sizeof(".text")+sizeof(".shstrtab");

struct MyElf {
  Elf32_Ehdr ehdr;
  Elf32_Shdr shzero; // zero section header
  Elf32_Shdr shstrn; // string section header
  Elf32_Shdr shtext; // text section header
  char strn[strn_size]; // string section
};

int main(int argc, const char *argv[]) {
  if (argc!=3) {
    cerr <<"Create an ELF file given a binary containing the .text section.\n"
         <<"Usage:\n"
         <<argv[0] <<" <bin_file> <elf_file>\n";
    return 1;
  }
  const char *binfile = argv[1];
  const char *elffile = argv[2];

  // ELF header
  MyElf elf;
  memcpy(elf.ehdr.e_ident,ELFMAG,4);
  elf.ehdr.e_ident[EI_CLASS] = ELFCLASS32;
  elf.ehdr.e_ident[EI_DATA] = ELFDATA2LSB;
  elf.ehdr.e_ident[EI_VERSION] = EV_CURRENT;
  elf.ehdr.e_ident[EI_OSABI] = ELFOSABI_STANDALONE;
  elf.ehdr.e_type = ET_NONE;
  elf.ehdr.e_machine = EM_ARM;
  elf.ehdr.e_version = EV_CURRENT;
  elf.ehdr.e_entry = 0x8000;
  elf.ehdr.e_phoff = 0; // no programm header
  elf.ehdr.e_shoff = (intptr_t)&elf.shzero - (intptr_t)&elf;
  elf.ehdr.e_flags = 0;
  elf.ehdr.e_ehsize = sizeof(Elf32_Ehdr);
  elf.ehdr.e_phentsize = sizeof(Elf32_Phdr);
  elf.ehdr.e_phnum = 0;
  elf.ehdr.e_shentsize = sizeof(Elf32_Shdr);
  elf.ehdr.e_shnum = 3;
  elf.ehdr.e_shstrndx = 1;

  // Fill the string section
  const int text_str_idx = 1;
  const int shstrtab_str_idx = text_str_idx + sizeof(".text");
  elf.strn[0] = '\0';
  strcpy(&elf.strn[text_str_idx],".text");
  strcpy(&elf.strn[shstrtab_str_idx],".shstrtab");

  // String section header
  elf.shstrn.sh_name = shstrtab_str_idx;
  elf.shstrn.sh_type = SHT_STRTAB;
  elf.shstrn.sh_flags = 0;
  elf.shstrn.sh_addr = 0;
  elf.shstrn.sh_offset = (intptr_t)&elf.strn - (intptr_t)&elf;
  elf.shstrn.sh_size = strn_size;
  elf.shstrn.sh_link = SHN_UNDEF;
  elf.shstrn.sh_info = 0;
  elf.shstrn.sh_addralign = 1;
  elf.shstrn.sh_entsize = 0;

  // get binary file size
  struct stat text_stat;
  int error = lstat(binfile,&text_stat);
  if (error) {
    cerr <<"Error: Cannot access \"" <<binfile <<"\": " <<strerror(errno) <<endl;
    abort();
  }
  const unsigned int text_size = text_stat.st_size;

  // zero section header
  elf.shzero.sh_name = 0;
  elf.shzero.sh_type = SHT_NULL;
  elf.shzero.sh_flags = 0;
  elf.shzero.sh_addr = 0;
  elf.shzero.sh_offset = 0;
  elf.shzero.sh_size = 0;
  elf.shzero.sh_link = SHN_UNDEF;
  elf.shzero.sh_info = 0;
  elf.shzero.sh_addralign = 0;
  elf.shzero.sh_entsize = 0;

  // .text section header
  elf.shtext.sh_name = text_str_idx;
  elf.shtext.sh_type = SHT_PROGBITS;
  elf.shtext.sh_flags = SHF_ALLOC|SHF_EXECINSTR;
  elf.shtext.sh_addr = 0x8000;
  elf.shtext.sh_offset = sizeof(MyElf);
  elf.shtext.sh_size = text_size;
  elf.shtext.sh_link = SHN_UNDEF;
  elf.shtext.sh_info = 0;
  elf.shtext.sh_addralign = 4;
  elf.shtext.sh_entsize = 0;

  // write to the ELF file
  ofstream ofs(elffile,ios::binary);
  if (!ofs) {
    cerr <<"Error: cannot open \"" <<elffile <<"\" for writing.\n";
    exit(1);
  }
  ofs.write(reinterpret_cast<const char *>(&elf),sizeof(elf));
  if (!ofs) {
    cerr <<"Error while writing.\n";
    abort();
  }
  ifstream ifs(binfile,ios::binary);
  if (!ifs) {
    cerr <<"Error: cannot open \"" <<binfile <<"\" for reading.\n";
    exit(1);
  }
  // load the binary file
  char *tmp = new char[text_size];
  ifs.read(tmp,text_size);
  if (!ifs) {
    cerr <<"Error while reading.\n";
    abort();
  }
  ofs.write(tmp,text_size);
  if (!ofs) {
    cerr <<"Error while writing.\n";
    abort();
  }
  ifs.close();
  ofs.close();

  return 0;
}
