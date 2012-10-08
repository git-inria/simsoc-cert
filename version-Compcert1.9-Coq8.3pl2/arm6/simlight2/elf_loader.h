#ifndef ELF_LOADER_HPP
#define ELF_LOADER_HPP

#include <stdio.h>
#include <elf.h>
#include "common.h"

struct Elf32_SectionHeader;

#define SECTIONS_MAX_SIZE 32

struct Elf32_Header {
  Elf32_Ehdr ehdr;
  struct Elf32_SectionHeader *sections[SECTIONS_MAX_SIZE];
  int sections_size;
  char * strings;
  struct Elf32_SectionHeader* text;
};

extern void eh_init_Elf32_Header(struct Elf32_Header *eh);
extern void eh_destruct_Elf32_Header(struct Elf32_Header *eh);
extern bool eh_is_elf(const struct Elf32_Header *eh);
extern bool eh_is_elf32(const struct Elf32_Header *eh);
extern bool eh_is_big_endian(const struct Elf32_Header *eh);
extern void eh_unencode(struct Elf32_Header *eh);
extern bool eh_is_exec(const struct Elf32_Header *eh);
extern void eh_load_sections(struct Elf32_Header *eh, FILE *ifs);

struct ElfFile {
  const char *file_name;
  FILE *ifs;
  struct Elf32_Header header;
};

extern void ef_init_ElfFile(struct ElfFile *ef, const char* elf_file);
extern void ef_destruct_ElfFile(struct ElfFile *ef);
extern bool ef_is_ARM(const struct ElfFile *ef);
extern bool ef_is_big_endian(const struct ElfFile *ef);
extern bool ef_is_elf32(const struct ElfFile *ef);
extern uint32_t ef_get_initial_pc(const struct ElfFile *ef);
extern uint32_t ef_get_text_start(const struct ElfFile *ef);
extern uint32_t ef_get_text_size(const struct ElfFile *ef);
extern void ef_load_sections(struct ElfFile *ef);

/* defined in simlight.c */
extern void elf_write_to_memory(const char *data, size_t start, size_t size);

#endif /* ELF_LOADER_HPP */
