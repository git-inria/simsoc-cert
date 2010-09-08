#include "elf_loader.h"
#include <iostream>
#include <cassert>
#include <cstring>
#include <cstdlib>

using namespace std;

struct NullStream: std::ostream
{
  NullStream(): std::ios(0), std::ostream(0) {}
};
NullStream null_stream;

ostream &debug() {return null_stream;}
ostream &info() {return null_stream;}
ostream &warning() {return cout;}
ostream &error() {return cout;}
#define HERE '[' <<__FILE__ <<':' <<std::dec <<__LINE__ <<"] "
#define UNREACHABLE assert(false && "this line should be unreachable");

struct Elf32_SectionHeader: public Elf32_Shdr {

  const char *name;

  void unencode() {
    assert(false && "big endian is not supported");
#if 0
    sh_name = bswap_32(sh_name);
    sh_type = bswap_32(sh_type);
    sh_flags = bswap_32(sh_flags);
    sh_addr = bswap_32(sh_addr);
    sh_offset = bswap_32(sh_offset);
    sh_size = bswap_32(sh_size);
    sh_link = bswap_32(sh_link);
    sh_info = bswap_32(sh_info);
    sh_addralign = bswap_32(sh_addralign);
    sh_entsize = bswap_32(sh_entsize);
#endif
  }

  size_t start() const {
    return sh_addr;
  }

  size_t size() const {
    return sh_size;
  }

  size_t file_offset() const {
    return sh_offset;
  }

  const char *str_type(Elf32_Half machine) {
    switch (sh_type) {
    case SHT_NULL: return "NULL";
    case SHT_PROGBITS: return "PROGBITS";
    case SHT_SYMTAB: return "SYMTAB";
    case SHT_STRTAB: return "STRTAB";
    case SHT_NOBITS: return "NOBITS";
    default:
      debug() <<HERE <<"sh_type = " <<hex <<sh_type <<endl;
      return "other";
    }
  }

  bool is_load() const {
    return (sh_flags&SHF_ALLOC) && sh_type==SHT_PROGBITS;
  }
};

Elf32_Header::Elf32_Header():
  sections(), strings(NULL), text(NULL) {}

Elf32_Header::~Elf32_Header() {
  for (size_t i = 0; i<sections.size(); ++i)
    delete sections[i];
  delete[] strings;
}

bool Elf32_Header::is_elf() const {
  return
    e_ident[EI_MAG0]==ELFMAG0 &&
    e_ident[EI_MAG1]==ELFMAG1 &&
    e_ident[EI_MAG2]==ELFMAG2 &&
    e_ident[EI_MAG3]==ELFMAG3;
}

bool Elf32_Header::is_elf32() const {
  return e_ident[EI_CLASS]==ELFCLASS32;
}

bool Elf32_Header::is_big_endian() const {
  return e_ident[EI_DATA]==ELFDATA2MSB;
}

void Elf32_Header::unencode() {
  if (!is_big_endian())
    return;
  assert(false && "big endian is not supported");
#if 0
  e_type = bswap_16(e_type);
  e_machine = bswap_16(e_machine);
  e_version = bswap_32(e_version);
  e_entry = bswap_32(e_entry);
  e_phoff = bswap_32(e_phoff);
  e_shoff = bswap_32(e_shoff);
  e_flags = bswap_32(e_flags);
  e_ehsize = bswap_16(e_ehsize);
  e_phentsize = bswap_16(e_phentsize);
  e_phnum = bswap_16(e_phnum);
  e_shentsize = bswap_16(e_shentsize);
  e_shnum = bswap_16(e_shnum);
  e_shstrndx = bswap_16(e_shstrndx);
#endif
}

bool Elf32_Header::is_exec() const {
  return e_type==ET_EXEC;
}

void Elf32_Header::load_sections(ifstream &ifs) {
  if (e_shentsize!=sizeof(Elf32_Shdr))
    UNREACHABLE;
  ifs.seekg(e_shoff);
  if (!ifs)
    UNREACHABLE;
  for (size_t i = 0; i<e_shnum; ++i) {
    sections.push_back(new Elf32_SectionHeader());
    ifs.read((char*) sections[i], sizeof(Elf32_Shdr));
    if (!ifs)
      UNREACHABLE;
    if (is_big_endian())
      sections[i]->unencode();
  }
  if (e_shstrndx>=sections.size())
    UNREACHABLE;
  strings = new char[sections[e_shstrndx]->size()];
  ifs.seekg(sections[e_shstrndx]->file_offset());
  if (!ifs)
    UNREACHABLE;
  ifs.read(strings,sections[e_shstrndx]->size());
  if (!ifs)
    UNREACHABLE;
  for (size_t i = 0; i<e_shnum; ++i) {
    sections[i]->name = strings+sections[i]->sh_name;
    debug() <<HERE <<"section " <<dec <<i <<": " <<sections[i]->name
           <<'\t' <<sections[i]->str_type(e_machine)
           <<(sections[i]->is_load()? " (load)": "")
           <<endl;
    if (!strcmp(".text",sections[i]->name))
      text = sections[i];
  }
  assert(text && "no \"text\" section found");
}

/******************************************************************************/
ElfFile::ElfFile(const char *elf_file):
  file_name(elf_file),
  ifs(file_name,ios::in|ios::binary)
{
  if (!ifs) {
    error() <<"failed to open file " <<file_name <<endl;
    exit(1);
  }
  ifs.read((char*) &header, sizeof(Elf32_Ehdr));
  if (!ifs)
    UNREACHABLE;
  if (!header.is_elf()) {
    error() <<file_name <<" is not an ELF file\n";
    exit(1);
  }
  assert(header.is_elf32() && "64-bits ELF not implemented");
  if (is_big_endian())
    header.unencode();
  header.load_sections(ifs);
}

ElfFile::~ElfFile() {
  ifs.close();
  debug() <<"destructor called" <<endl;
}

bool ElfFile::is_ARM() const {
  return header.e_machine==EM_ARM;
}

bool ElfFile::is_big_endian() const {
  return header.is_big_endian();
}

uint32_t ElfFile::get_initial_pc() const {
  if (!header.is_exec()) {
    error() <<file_name <<" is not an executable ELF file\n";
    exit(1);
  }
  return header.e_entry;
}

uint32_t ElfFile::get_text_start() const {
  return header.text->sh_addr;
}

uint32_t ElfFile::get_text_size() const {
  return header.text->size();
}

void ElfFile::load_sections() {
  for (size_t i = 0; i<header.sections.size(); ++i) {
    if (header.sections[i]->is_load()) {
      uint32_t mem_start = header.sections[i]->start();
      uint32_t mem_size = header.sections[i]->size();
      uint32_t mem_end = mem_start+mem_size;
      assert((mem_start&3)==0 && (mem_size&3)==0 && "section not aligned on word boundaries");
      ifs.seekg(header.sections[i]->file_offset());
      if (!ifs)
        UNREACHABLE;
      info() <<hex <<"write from " <<mem_start <<" to "
             <<mem_end <<endl;
      char * tmp = new char[mem_size];
      ifs.read(tmp, mem_size);
      if (!ifs)
        UNREACHABLE;
      write_to_memory(tmp,mem_start,mem_size);
      delete[] tmp;
    }
  }
}
