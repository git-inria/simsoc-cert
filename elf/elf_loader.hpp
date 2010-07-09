#ifndef ELF_LOADER_HPP
#define ELF_LOADER_HPP

#include <fstream>
#include <vector>
#include "elf.h"

struct Elf32_SectionHeader;

struct Elf32_Header: public Elf32_Ehdr {
  std::vector<Elf32_SectionHeader*> sections;
  char * strings;
  Elf32_SectionHeader* text;
  Elf32_Header();
  ~Elf32_Header();
  bool is_elf() const;
  bool is_elf32() const;
  bool is_big_endian() const;
  void unencode();
  bool is_exec() const;
  void load_sections(std::ifstream &ifs);
};

class ElfFile {
public:

  const char* file_name;

  ElfFile(const char* elf_file);

  ~ElfFile();

  bool is_ARM() const;

  bool is_big_endian() const;

  bool is_elf32() const {return header.is_elf32();}

  uint32_t get_start_address() const;

  uint32_t get_text_start() const;

  uint32_t get_text_size() const;

  void load_sections();

  virtual void write_to_memory(const char *data, size_t start, size_t size) = 0;

protected:
  std::ifstream ifs;

  Elf32_Header header;
};

#endif //ELF_LOADER_HPP
