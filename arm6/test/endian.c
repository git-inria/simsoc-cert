/* Derived from SimSoC, Copyright © INRIA 2007, 2008, 2009, 2010
 * LGPL license version 3 */

/* endianness related test
 * After 96 instructions executed, r0 should contain 7 */

#include "common.h"

int good = 0;
int bad = 0;

typedef struct {
  uint16_t h0;
  uint16_t h1;
} Half;

typedef struct {
  uint8_t b0;
  uint8_t b1;
  uint8_t b2;
  uint8_t b3;
} Byte;

typedef union {
  uint32_t word;
  Half     half;
  Byte     byte;
} Data;

int main()
{
  Data d;
  d.word = 0xa0b0c0d0;

  uint8_t big_endian;
  if (d.half.h0==0xa0b0&&
      d.half.h1==0xc0d0) {
    if (!(d.byte.b0==0xa0&&
          d.byte.b1==0xb0&&
          d.byte.b2==0xc0&&
          d.byte.b3==0xd0)) {
      bad+=1; //print_str("=> error!\n");
      return (bad<<16)|good;
    }
    bad+=2; //print_str("=> big endian\n");
    big_endian = 1;
  } else if (d.half.h0==0xc0d0&&
             d.half.h1==0xa0b0&&
             d.byte.b0==0xd0&&
             d.byte.b1==0xc0&&
             d.byte.b2==0xb0&&
             d.byte.b3==0xa0) {
    good+=1; /* print_str("=> little endian\n"); */
    big_endian = 0;
  } else {
    bad+=4; /* print_str("=> error!\n"); */
    return (bad<<16)|good;
  }

  Data a;
  a.byte.b0 = 0xa0;
  a.byte.b1 = 0xb0;
  a.byte.b2 = 0xc0;
  a.byte.b3 = 0xd0;

  if (a.half.h0==0xa0b0&&
      a.half.h1==0xc0d0) {
    if (a.word!=0xa0b0c0d0) {
      bad+=8; /* print_str("=> error!\n"); */
      return (bad<<16)|good;
    }
    bad+=16; /* print_str("=> big endian\n"); */
    if (!big_endian) {
      bad+=32; /* print_str("=> error!\n"); */
      return (bad<<16)|good;
    }
  } else if (a.half.h0==0xb0a0&&
             a.half.h1==0xd0c0){
    if(a.word!=0xd0c0b0a0) {
      bad+=64; /* print_str("=> error!\n"); */
      return (bad<<16)|good;
    }
    good+=2; /* print_str("=> little endian\n"); */
    if (big_endian) {
      bad+=128; /* print_str("=> error!\n"); */
      return (bad<<16)|good;
    }
  } else {
    bad+=256; /* print_str("=> error!\n"); */
    return (bad<<16)|good;
  }
  good+=4; /* print_str("End of Test.\n"); */
  return (bad<<16)|good;
}
