// SimSoC-Cert, a library on processor architectures for embedded systems.
// See the COPYRIGHTS and LICENSE files.

// Interface between the ISS and the memory(/MMU)

#include "arm_mmu.hpp"
#include <string.h>
#include <assert.h>

void init_MMU(MMU *mmu, uint32_t begin, uint32_t size) {
  assert((begin&3)==0 && "memory start not aligned on a word boundary");
  assert((size&3)==0 && "memory size not aligned on a word boundary");
  mmu->begin = begin;
  mmu->size = size;
  mmu->end = begin+size;
  mmu->mem = (uint8_t*) calloc(size,1);
}

void destruct_MMU(MMU *mmu) {
  free(mmu->mem);
}

uint8_t read_byte(MMU *mmu, uint32_t addr) {
  assert(mmu->begin<=addr && addr<mmu->end && "out of memory access");
  DEBUG(<<"read byte " <<std::hex <<(uint32_t)mmu->mem[addr-mmu->begin]
        <<" from " <<addr <<'\n');
  return mmu->mem[addr-mmu->begin];
}

uint16_t read_half(MMU *mmu, uint32_t addr) {
  assert(mmu->begin<=addr && addr<mmu->end && "out of memory access");
  assert((addr&1)==0 && "misaligned acces");
  union {
    uint16_t half;
    uint8_t bytes[2];
  } tmp;
  memcpy(tmp.bytes,mmu->mem+(addr-mmu->begin),2);
  DEBUG(<<"read half " <<std::hex <<tmp.half <<" from " <<addr <<'\n');
  return tmp.half;
}

uint32_t read_word(MMU *mmu, uint32_t addr) {
  assert(mmu->begin<=addr && addr<mmu->end && "out of memory access");
  assert((addr&3)==0 && "misaligned acces");
  union {
    uint32_t word;
    uint8_t bytes[4];
  } tmp;
  memcpy(tmp.bytes,mmu->mem+(addr-mmu->begin),4);
  DEBUG(<<"read " <<std::hex <<tmp.word <<" from " <<addr <<'\n');
  return tmp.word;
}

void write_byte(MMU *mmu, uint32_t addr, uint8_t data) {
  assert(mmu->begin<=addr && addr<mmu->end && "out of memory access");
  mmu->mem[addr-mmu->begin] = data;
  DEBUG(<<"write byte " <<std::hex <<(uint32_t) data <<" to " <<addr <<'\n');
}

void write_half(MMU *mmu, uint32_t addr, uint16_t data) {
  assert(mmu->begin<=addr && addr<mmu->end && "out of memory access");
  assert((addr&1)==0 && "misaligned acces");
  union {
    uint16_t half;
    uint8_t bytes[2];
  } tmp;
  tmp.half = data;
  memcpy(mmu->mem+(addr-mmu->begin),tmp.bytes,2);
  DEBUG(<<"write half " <<std::hex <<tmp.half <<" to " <<addr <<'\n');
}

void write_word(MMU *mmu, uint32_t addr, uint32_t data) {
  assert(mmu->begin<=addr && addr<mmu->end && "out of memory access");
  assert((addr&3)==0 && "misaligned acces");
  union {
    uint32_t word;
    uint8_t bytes[4];
  } tmp;
  tmp.word = data;
  memcpy(mmu->mem+(addr-mmu->begin),tmp.bytes,4);
  DEBUG(<<"write " <<std::hex <<tmp.word <<" to " <<addr <<'\n');
}
