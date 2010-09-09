#include "elf_loader.h"
#include <assert.h>
#include <string.h>
#include <stdlib.h>

#define UNREACHABLE assert(false && "this line should be unreachable");

struct Elf32_SectionHeader {
  Elf32_Shdr shdr;
  const char *name;
};

static void esh_unencode(struct Elf32_SectionHeader *esh) {
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

static size_t esh_start(const struct Elf32_SectionHeader *esh) {
  return esh->shdr.sh_addr;
}

static size_t esh_size(const struct Elf32_SectionHeader *esh) {
  return esh->shdr.sh_size;
}

static size_t esh_file_offset(const struct Elf32_SectionHeader *esh) {
  return esh->shdr.sh_offset;
}

static const char *esh_str_type(const struct Elf32_SectionHeader *esh,
                                Elf32_Half machine) {
  switch (esh->shdr.sh_type) {
  case SHT_NULL: return "NULL";
  case SHT_PROGBITS: return "PROGBITS";
  case SHT_SYMTAB: return "SYMTAB";
  case SHT_STRTAB: return "STRTAB";
  case SHT_NOBITS: return "NOBITS";
  default:
    return "other";
  }
}

static bool esh_is_load(const struct Elf32_SectionHeader *esh) {
  return (esh->shdr.sh_flags&SHF_ALLOC) && esh->shdr.sh_type==SHT_PROGBITS;
}

void eh_init_Elf32_Header(struct Elf32_Header *eh) {
  eh->sections_size = 0;
  eh->strings = NULL;
  eh->text = NULL;
}

void eh_destruct_Elf32_Header(struct Elf32_Header *eh) {
  int i;
  for (i = 0; i<eh->sections_size; ++i) {
    free(eh->sections[i]);
  }
  free(eh->strings);
}

bool eh_is_elf(const struct Elf32_Header *eh) {
  return
    eh->ehdr.e_ident[EI_MAG0]==ELFMAG0 &&
    eh->ehdr.e_ident[EI_MAG1]==ELFMAG1 &&
    eh->ehdr.e_ident[EI_MAG2]==ELFMAG2 &&
    eh->ehdr.e_ident[EI_MAG3]==ELFMAG3;
}

bool eh_is_elf32(const struct Elf32_Header *eh) {
  return eh->ehdr.e_ident[EI_CLASS]==ELFCLASS32;
}

bool eh_is_big_endian(const struct Elf32_Header *eh) {
  return eh->ehdr.e_ident[EI_DATA]==ELFDATA2MSB;
}

void eh_unencode(struct Elf32_Header *eh) {
  if (!eh_is_big_endian(eh))
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

bool eh_is_exec(const struct Elf32_Header *eh) {
  return eh->ehdr.e_type==ET_EXEC;
}

void eh_load_sections(struct Elf32_Header *eh, FILE *ifs) {
  int error;
  size_t i;
  size_t count;
  if (eh->ehdr.e_shentsize!=sizeof(Elf32_Shdr))
    UNREACHABLE;
  error = fseek(ifs,eh->ehdr.e_shoff,SEEK_SET);
  if (error)
    UNREACHABLE;
  for (i = 0; i<eh->ehdr.e_shnum; ++i) {
    assert(eh->sections_size<SECTIONS_MAX_SIZE &&
           "please increase the constant given in the header file");
    ++eh->sections_size;
    eh->sections[i] =
      (struct Elf32_SectionHeader*) malloc(sizeof(struct Elf32_SectionHeader));
    count = fread((void*) &eh->sections[i]->shdr, 1, sizeof(Elf32_Shdr), ifs);
    if (count!=sizeof(Elf32_Shdr))
      UNREACHABLE;
    if (eh_is_big_endian(eh))
      esh_unencode(eh->sections[i]);
  }
  if (eh->ehdr.e_shstrndx>=eh->sections_size)
    UNREACHABLE;
  eh->strings = (char*) calloc(esh_size(eh->sections[eh->ehdr.e_shstrndx]),1);
  error = fseek(ifs,esh_file_offset(eh->sections[eh->ehdr.e_shstrndx]),SEEK_SET);
  if (error)
    UNREACHABLE;
  count = fread((void*) eh->strings, 1,
                esh_size(eh->sections[eh->ehdr.e_shstrndx]),
                ifs);
  if (count!=esh_size(eh->sections[eh->ehdr.e_shstrndx]))
    UNREACHABLE;
  for (i = 0; i<eh->ehdr.e_shnum; ++i) {
    eh->sections[i]->name = eh->strings+eh->sections[i]->shdr.sh_name;
/*     debug() <<HERE <<"section " <<dec <<i <<": " <<sections[i]->name */
/*            <<'\t' <<sections[i]->str_type(e_machine) */
/*            <<(sections[i]->is_load()? " (load)": "") */
/*            <<endl; */
    if (!strcmp(".text",eh->sections[i]->name))
      eh->text = eh->sections[i];
  }
  assert(eh->text && "no \"text\" section found");
}

/******************************************************************************/
void ef_init_ElfFile(struct ElfFile *ef, const char *elf_file) {
  size_t count;
  eh_init_Elf32_Header(&ef->header);
  ef->file_name = elf_file;
  ef->ifs = fopen(ef->file_name,"rb");
  if (!ef->ifs) {
    fprintf(stderr,"failed to open file \"%s\"\n",ef->file_name);
    exit(1);
  }
  count = fread((void*) &ef->header.ehdr, 1, sizeof(Elf32_Ehdr), ef->ifs);
  if (count!=sizeof(Elf32_Ehdr))
    UNREACHABLE;
  if (!eh_is_elf(&ef->header)) {
    fprintf(stderr,"\"%s\" is not an ELF file\n",ef->file_name);
    exit(1);
  }
  assert(eh_is_elf32(&ef->header) && "64-bits ELF not implemented");
  if (ef_is_big_endian(ef))
    eh_unencode(&ef->header);
  eh_load_sections(&ef->header,ef->ifs);
}

void ef_destruct_ElfFile(struct ElfFile *ef) {
  fclose(ef->ifs);
}

bool ef_is_ARM(const struct ElfFile *ef) {
  return ef->header.ehdr.e_machine==EM_ARM;
}

bool ef_is_big_endian(const struct ElfFile *ef) {
  return eh_is_big_endian(&ef->header);
}

bool ef_is_elf32(const struct ElfFile *ef) {
  return eh_is_elf32(&ef->header);
}

uint32_t ef_get_initial_pc(const struct ElfFile *ef) {
  if (!eh_is_exec(&ef->header)) {
    fprintf(stderr,"\"%s\" is not an executable ELF file\n",ef->file_name);
    exit(1);
  }
  return ef->header.ehdr.e_entry;
}

uint32_t ef_get_text_start(const struct ElfFile *ef) {
  return ef->header.text->shdr.sh_addr;
}

uint32_t ef_get_text_size(const struct ElfFile *ef) {
  return esh_size(ef->header.text);
}

void ef_load_sections(struct ElfFile *ef) {
  int error;
  size_t count;
  int i;
  for (i = 0; i<ef->header.sections_size; ++i) {
    if (esh_is_load(ef->header.sections[i])) {
      uint32_t mem_start = esh_start(ef->header.sections[i]);
      uint32_t mem_size = esh_size(ef->header.sections[i]);
      uint32_t mem_end = mem_start+mem_size;
      assert((mem_start&3)==0 && (mem_size&3)==0 &&
             "section not aligned on word boundaries");
      error = fseek(ef->ifs,esh_file_offset(ef->header.sections[i]),SEEK_SET);
      if (error)
        UNREACHABLE;
/*       info() <<hex <<"write from " <<mem_start <<" to " */
/*              <<mem_end <<endl; */
      char * tmp = (char*) calloc(mem_size,1);
      count = fread((void*) tmp, 1, mem_size, ef->ifs);
      if (count!=mem_size)
        UNREACHABLE;
      elf_write_to_memory(tmp,mem_start,mem_size);
      free(tmp);
    }
  }
}
