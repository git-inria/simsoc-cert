/* Derived from SimSoC, Copyright © INRIA 2007, 2008, 2009, 2010
 * LGPL license version 3 */

/* test various cryptography algorithms
 * After 9,534,246 instructions executed, r0 should contain 127 = 0x7f */

#include <string.h>
#include <stdlib.h>
#include <stdio.h>

#include "common.h"

#include "aes.h"
#include "sha2.h"
#include "sha4.h"
#include "des.h"
#include "arc4.h"
#include "md5.h"
#include "base64.h"
#include "havege.h"
#include "bignum.h"
#include "rsa.h"

int count = 0;
int error = 0;

#define CHECK(OP, TEST)                         \
  if ((TEST)) count+=(OP);

#define KEY_SIZE 1024
#define EXPONENT 65537

/* Increase to measure performance...
   Data size must be a multiple of 32 */

#define DATA_SIZE 4096
#define BASE64_BUFSIZE DATA_SIZE + (DATA_SIZE>>1)
#define LOOPS 32

const unsigned char key_32[32] = { 0xe4, 0xa8, 0x6c, 0xf0, 0xf4, 0xb8, 0x7c,
                                   0xd3, 0x97, 0x5b, 0x0f, 0xe3, 0xa7, 0x6b,
                                   0xc2, 0x86, 0x4a, 0x1e, 0xd2, 0x96, 0x5a,
                                   0xb1, 0x75, 0x39, 0x2d, 0xc1, 0x85, 0x49 };

unsigned char key_64[64] = { 0xF3, 0xF6, 0x75, 0x2A, 0xE8, 0xD7, 0x83, 0x11,
			     0x38, 0xF0, 0x41, 0x56, 0x06, 0x31, 0xB1, 0x14,
			     0x8B, 0x79, 0xEE, 0xCC, 0x93, 0xA0, 0xEE, 0x5D,
			     0xFF, 0x30, 0xB4, 0xEA, 0x21, 0x63, 0x6D, 0xA4,
			     0xF3, 0xF6, 0x75, 0x2A, 0xE8, 0xD7, 0x83, 0x11,
			     0x38, 0xF0, 0x41, 0x56, 0x06, 0x31, 0xB1, 0x14,
			     0x8B, 0x79, 0xEE, 0xCC, 0x93, 0xA0, 0xEE, 0x5D,
			     0xFF, 0x30, 0xB4, 0xEA, 0x21, 0x63, 0x6D, 0xA4 };

const unsigned char iv_16[16] = { 'v', 'a', 'n', 'i', 'j', 'o', 'l', 'b',
                                  'f', 'c', 'l', 'u', 'd', 'e', 'h', 'm' };

const unsigned char iv_32[32] =  { 0x48, 0xE3, 0x1E, 0x9E, 0x25, 0x67, 0x18, 0xF2,
                                   0x92, 0x29, 0x31, 0x9C, 0x19, 0xF1, 0x5B, 0xA4,
                                   0x05, 0x8C, 0xCF, 0xFD, 0xBB, 0xCB, 0x38, 0x2D,
                                   0x1F, 0x6F, 0x56, 0x58, 0x5D, 0x8A, 0x4A, 0xDE,
};

unsigned char plain[DATA_SIZE];
unsigned char cipher[DATA_SIZE];
unsigned char deciphered[DATA_SIZE];
unsigned char base64_cipher[BASE64_BUFSIZE];

const unsigned long check_enc_key[96] = {0x2018152b, 0x3f392311, 0x17331530, 0x8271e3d, 0x16251c3a, 0x2d171620, 0x3411171c, 0x341e3130, 0x1935133c, 0x170e2a0b, 0x390f1d27, 0x25032c2a, 0x34262037, 0xe0b053a, 0x52c3215, 0x2e262727, 0x3b021227, 0x1133390a, 0x2e16220b, 0x1e333d2b, 0xe0a291f, 0x1f140d0d, 0x283f3b22, 0x18140517, 0x18170a21, 0x3b201b35, 0x3a3a2e1e, 0x92a1a31, 0x23321d1a, 0x2f121b16, 0x1d072b38, 0x42d233c, 0x1c3b3214, 0xf332232, 0x343d0518, 0x36392c2a, 0x2329062c, 0x2b173628, 0x373e0520, 0xf2c3218, 0x2c171d08, 0x232b2614, 0x393c2c18, 0x3d05121d, 0x53b2c01, 0x1f1a3331, 0x3a160823, 0x2e1f0317, 0xb2f230a, 0x231d1324, 0x2f38202b, 0x3e2c1c14, 0x24262b01, 0x373b1c0e, 0x3b3c220d, 0x2913200f, 0x133f2005, 0x17283506, 0x28153407, 0x2e3e040a, 0x362e1415, 0x3d062a0e, 0x1f181333, 0x332e2408, 0x3f0e0d3b, 0x2825352e, 0x211f1e1c, 0x251b2f35, 0x35141d16, 0x1f093a1b, 0x2d2c1e2f, 0x327371a, 0x263f250d, 0x26052f3b, 0x14292f37, 0x2b3c260f, 0x332d3e21, 0x302e2d3e, 0x1b112213, 0x263b3e3d, 0x141e3937, 0x3e203d07, 0xa3c382f, 0x92e213f, 0x23372b15, 0x2530173f, 0x32303c3d, 0x3b391e17, 0x2f2c3f0b, 0x331a1236, 0x291a273d, 0x361d3b14, 0xd2b352e, 0x1b293a2f, 0x1b303e32, 0x2f0e133d };

const unsigned long check_dec_key[96] = {0x1b303e32, 0x2f0e133d, 0xd2b352e, 0x1b293a2f, 0x291a273d, 0x361d3b14, 0x2f2c3f0b, 0x331a1236, 0x32303c3d, 0x3b391e17, 0x23372b15, 0x2530173f, 0xa3c382f, 0x92e213f, 0x141e3937, 0x3e203d07, 0x1b112213, 0x263b3e3d, 0x332d3e21, 0x302e2d3e, 0x14292f37, 0x2b3c260f, 0x263f250d, 0x26052f3b, 0x2d2c1e2f, 0x327371a, 0x35141d16, 0x1f093a1b, 0x211f1e1c, 0x251b2f35, 0x3f0e0d3b, 0x2825352e, 0x1f181333, 0x332e2408, 0x362e1415, 0x3d062a0e, 0x28153407, 0x2e3e040a, 0x133f2005, 0x17283506, 0x3b3c220d, 0x2913200f, 0x24262b01, 0x373b1c0e, 0x2f38202b, 0x3e2c1c14, 0xb2f230a, 0x231d1324, 0x3a160823, 0x2e1f0317, 0x53b2c01, 0x1f1a3331, 0x393c2c18, 0x3d05121d, 0x2c171d08, 0x232b2614, 0x373e0520, 0xf2c3218, 0x2329062c, 0x2b173628, 0x343d0518, 0x36392c2a, 0x1c3b3214, 0xf332232, 0x1d072b38, 0x42d233c, 0x23321d1a, 0x2f121b16, 0x3a3a2e1e, 0x92a1a31, 0x18170a21, 0x3b201b35, 0x283f3b22, 0x18140517, 0xe0a291f, 0x1f140d0d, 0x2e16220b, 0x1e333d2b, 0x3b021227, 0x1133390a, 0x52c3215, 0x2e262727, 0x34262037, 0xe0b053a, 0x390f1d27, 0x25032c2a, 0x1935133c, 0x170e2a0b, 0x3411171c, 0x341e3130, 0x16251c3a, 0x2d171620, 0x17331530, 0x8271e3d, 0x2018152b, 0x3f392311 };


#define HEAP_SIZE 8*1024
#define HEAP_MAGIC 0xfedc
#define FREELIST_ERROR_COUNT 1
#define FREELIST_ERROR_SIZE  2

typedef struct _chunk {
  unsigned int magic;
  size_t size;
  struct _chunk *next;
} Chunk;

unsigned char heap[HEAP_SIZE];
Chunk *freelist;
int init_heap = 0;
int chunk_count = 0;
int allocated = 0;

static unsigned long dummy_clock = 0;
static int delays [4] = { 1, 2, 3, 4};
static int clock_count = 0;
static int clock_incr = 0;

unsigned long hardclock( void )
{
  int index = clock_incr % 4;
  dummy_clock += delays[index];
  if (clock_incr == 8192) {
    clock_count += clock_incr;
    /*     print_str("clock : "); print_int(clock_count); */
    /*     print_str(" value : "); print_int(dummy_clock); */
    /*     EOL; */
    clock_incr = 0;
  }
  ++clock_incr;
  return dummy_clock;
}

int rand() {
  static int index = 0;
  return (int) key_64[index++ % 63 ];
}

void init_malloc() {

  if (init_heap == 0) { /* init first time */
    freelist = (Chunk *) heap;
    freelist->magic = HEAP_MAGIC;
    freelist->next = NULL;
    freelist->size = HEAP_SIZE - sizeof(Chunk);
    allocated = 0;
    chunk_count = 1;
    init_heap = 1;
  }
}
/* routine to check invariants */

int check_freelist(int verbose) {
  Chunk *current;
  int count = 0;
  int size = 0;
  int ret = 0;
  for (current = freelist; current != NULL; current=current->next) {
    ++count;
    size += current->size + sizeof(Chunk);
  }
  if (count != chunk_count) {
    ret = FREELIST_ERROR_COUNT;
  }
  if ((size + allocated) != HEAP_SIZE) {
    ret = FREELIST_ERROR_SIZE;
  }
  return ret;
}

void * malloc(size_t sz)
{
  Chunk *current;
  Chunk *previous;
  char *ret;

  if (sz == 0 || freelist == NULL) {
    return NULL;
  }
  /* align on 32 bits */
  if (sz & 0x3) {
    sz = ((sz >> 2) + 1) << 2;
  }
  for (current=freelist, previous=freelist;
       sz > current->size;
       previous = current, current=current->next) {
    if (current->next == NULL){
      return NULL;
    }
  }
  ret = (char *)current + sizeof(Chunk);
  if (sz == current->size || (sz + sizeof(Chunk)) >= current->size ) {
    if (previous == current)  /* the first item in free list fits */
      freelist = current->next;
    else
      previous->next = current->next;
    --chunk_count;
  }
  else {
    char *addr = ret + sz;
    Chunk *new = (Chunk *) addr;
    new->magic = HEAP_MAGIC;
    new->size = current->size - sz - sizeof(Chunk);
    current->size = sz;
    new->next = current->next;
    if (previous == current)
      freelist = new;
    else
      previous->next = new;
  }
  allocated += current->size + sizeof(Chunk);
  /* check_freelist(1); */
  return (void *) ret;
}


void free(void * f)
{
  char *addr = (char*) f - sizeof(Chunk);
  Chunk *freed = (Chunk *) addr;
  Chunk *current = freelist;
  Chunk *previous = freelist;

  if (f == NULL) {
    /*     print_str("freeing NULL illegal\n"); */
    ++error;
    return;
  }
  if (freed->magic != HEAP_MAGIC) {
    /*  print_str("bogus free\n"); */
    return;
  }
  if (freelist == NULL) {
    freelist = freed;
    freelist->next = NULL;
    allocated = allocated - (freed->size+sizeof(Chunk));
    chunk_count = 1;
  }
  else {
    for (current=freelist, previous=freelist; freed > current;
	 previous=current, current=current->next) {
      if (current->next == NULL)
	break;
    }
    if (freed == current) {
      /* print_str("already free\n"); */
      return;
    }
    allocated = allocated - (freed->size+sizeof(Chunk));
    if (freed < current) {
      if (current == previous)
	freelist = freed;
      else
	previous->next = freed;
      if (addr + freed->size + sizeof(Chunk) == (char *)current){
	/* print_str("merge next chunk\n"); */
	freed->size += current->size + sizeof(Chunk);
	freed->next = current->next;
      }
      else {
	freed->next = current;
	++chunk_count;
      }
    }
    else {
      /* print_str("appending a chunk to freelist ... "); */
      if ((char *)current + current->size + sizeof(Chunk) == (char *)freed){
	/* print_str("merge last chunk\n"); */
	current->size += freed->size + sizeof(Chunk);
	current->next = NULL;
      }
      else {
	freed->next = NULL;
	current->next = freed;
	++chunk_count;
      }
    }
  }
  /* check_freelist(1); */
}


#define TEST_SIZE 16
void test_malloc() {
  char * addresses[TEST_SIZE];
  char * addr;
  int i;

  /* allocate more than max */
  if (malloc(HEAP_SIZE) != NULL) {
    /*     print_str("major heap size bug\n"); */
    ++error;
  }
  /* malloc all memory available */
  if ((addr = malloc(HEAP_SIZE-sizeof(Chunk))) == NULL) {
    /*     print_str("bug allocating heap\n"); */
    ++error;
  } else if (chunk_count != 0) {
    ++error;
    /*     print_str("bug in chunk count on first malloc\n"); */
    /* malloc now should fail, then free */
  }
  if (malloc(TEST_SIZE) != NULL) {
    ++error;
    /*     print_str("error: malloc should return NULL\n"); */
  } else {
    free(addr);
    if (chunk_count != 1) {
      ++error;
      /*       print_str("error: chunk count not back to 1\n"); */
    }
  }
  /* Now heap is back one big chunk */
  for (i = 0; i < TEST_SIZE; ++i) {
    if ((addresses[i] = malloc(i+1)) == NULL) {
      ++error;
      /*       print_str("cannot malloc increasing size\n"); */
    }
    if (chunk_count != 1) {
      ++error;
      /*       print_str("chunk_count error : "); */
      /*       print_int(chunk_count); */
      /*       EOL; */
    }
  }
  for (i=0; i< TEST_SIZE; ++i)
    free(addresses[i]);
  if (chunk_count != TEST_SIZE ) {
    ++error;
    /*     print_str("error in chunk count : "); */
    /*     print_int(chunk_count); EOL; */
  }
  /* free again should do nothing */
  for (i=0; i< TEST_SIZE; ++i)
    free(addresses[i]);
  if (chunk_count != TEST_SIZE) {
    ++error;
    /*     print_str("error in multiple free : "); */
    /*     print_int(chunk_count); */
    /*     EOL; */
  }
  /* loop malloc and free until not possible */
  for (i=16; (addr=malloc(i))!= NULL ; i += 2) {
    free(addr);
    if (check_freelist(0) != 0) {
      ++error;
      /*       print_str("malloc free loop error"); */
      break;
    }
  }
  /* malloc largest possible */
  if ((addr = malloc(i-2)) == NULL) {
    ++error;
    /*     print_str("error in allocating max\n"); */
  }
  else {
    free(addr);
  }
  if (check_freelist(0) != 0) {
    ++error;
    /*     print_str("malloc free max error"); */
  }
}


void test_aes() {
  int i,j;
  unsigned char digest[32];
  unsigned char IV[16];
  unsigned char enc_key[32], dec_key[32];
  sha2_context sha_ctx;
  aes_context aes_ctx;

  for (i=0; i < DATA_SIZE; i += 64) {
    for (j = 0; j < 64 ; ++j)
      plain[i+j] = (i+j % 256) ^ key_64[j] ;
  }
  memset(cipher, 0, DATA_SIZE);
  memset(deciphered, 0, DATA_SIZE);

  /*
   * Hash the IV and the secret key together LOOPS times
   * using the result to setup the AES context and HMAC.
   */
  memset(digest, 0,  32 );
  memcpy(IV, iv_16, 16);
  memcpy(digest, iv_32, 32 );
  memcpy(enc_key, key_32, 32);
  for( i = 0; i < LOOPS ; i++ )
    {
      sha2_starts( &sha_ctx, 0 );
      sha2_update( &sha_ctx, digest, 32);
      sha2_update( &sha_ctx, enc_key, 32);
      sha2_finish( &sha_ctx, digest );
    }
  memcpy(enc_key, digest, 32);

  aes_setkey_enc( &aes_ctx, digest, 256 );
  /*
   * Encrypt and write the ciphertext.
   */
  aes_crypt_cbc(&aes_ctx, AES_ENCRYPT, DATA_SIZE,
		IV, plain, cipher );
  /*
   * Hash again the IV and the secret key together LOOPS times
   * using the result to setup the AES context and HMAC.
   * This should yield same result
   */
  memset(digest, 0,  32 );
  memcpy(IV, iv_16, 16);
  memcpy(digest, iv_32, 32 );
  memcpy(dec_key, key_32, 32);
  for( i = 0; i < LOOPS ; i++ )
    {
      sha2_starts( &sha_ctx, 0 );
      sha2_update( &sha_ctx, digest, 32 );
      sha2_update( &sha_ctx, dec_key, 32 );
      sha2_finish( &sha_ctx, digest );
    }
  if (memcmp(enc_key, digest, 32) != 0) {
    ++error;
    /*     print_str("Error AES enc key != dec key\n"); */
  }
  aes_setkey_dec( &aes_ctx, digest, 256 );
  /*
   * Decrypt
   */
  aes_crypt_cbc(&aes_ctx, AES_DECRYPT, DATA_SIZE,
		IV, cipher, deciphered );
  /*
   * Verify the message
   */
  if( memcmp(deciphered, plain, DATA_SIZE ) == 0 ) {
    /*     print_str( "AES encrypt-decrypt OK\n"); */
    count+=1;
  } else {
    /*     print_str("AES encrypt-decrypt KO\n"); */
    ++error;
  }
}

void test_sha4() {
  unsigned char hmac1[64], hmac2[64];

  /* Compute SHA4 hash code of messages */
  sha4_hmac(key_64, 64, plain, DATA_SIZE, hmac1, 0);
  sha4_hmac(key_64, 64, deciphered, DATA_SIZE, hmac2, 0);
  if( memcmp(hmac1, hmac2, 64 ) == 0 ) {
    count+=2;
    /*     print_str( "SHA4 OK\n"); */
  } else {
    /*     print_str("SHA4 KO\n"); */
    ++error;
  }
}

void test_sha2(unsigned char * enc_key, unsigned char * dec_key) {
  unsigned char digest[32];
  unsigned char IV[16];
  sha2_context sha_ctx;
  int i;

  /* Generate DES keys with SHA2.
     The two keys should be identical */
  memcpy(IV, iv_16, 16);
  memcpy(digest, iv_32, 32 );
  memcpy(enc_key, key_32, 32);
  for( i = 0; i < LOOPS ; i++ )
    {
      sha2_starts( &sha_ctx, 0 );
      sha2_update( &sha_ctx, digest, 32);
      sha2_update( &sha_ctx, enc_key, 32);
      sha2_finish( &sha_ctx, digest );
    }
  memcpy(enc_key, digest, 32);

  memcpy(IV, iv_16, 16);
  memcpy(digest, iv_32, 32 );
  memcpy(dec_key, key_32, 32);
  for( i = 0; i < LOOPS ; i++ )      {
    sha2_starts( &sha_ctx, 0 );
    sha2_update( &sha_ctx, digest, 32);
    sha2_update( &sha_ctx, dec_key, 32);
    sha2_finish( &sha_ctx, digest );
  }
  memcpy(dec_key, digest, 32);

  if (memcmp(enc_key, dec_key, 32) == 0) {
    count+=4;
    /*     print_str("SHA2 OK\n"); */
  } else {
    /*     print_str("SHA2 KO... DES will fail\n"); */
    ++error;
  }
}

void test_des(unsigned char * enc_key, unsigned char * dec_key) {
  des3_context des_ctx;
  unsigned char IV[16];

  /* Now DES encryption */
  des3_set3key_enc(&des_ctx, enc_key);
  /* Verify the enc key
     for (i=0; i<96; ++i) {
     if (des_ctx.sk[i] != check_enc_key[i]) {
     print_str("error encrypt des3 key at ");
     print_int(i);
     EOL;
     print_str("should be :"); print_hex_uint(check_enc_key[i]);EOL;
     print_str("value :"); print_hex_uint(des_ctx.sk[i]);EOL;
     break;
     }
     }
  */

  /* encrypt */
  memcpy(IV, iv_16, 16);
  des3_crypt_cbc(&des_ctx, DES_ENCRYPT, DATA_SIZE, IV, plain, cipher);

  /* Set decryption key */
  des3_set3key_dec(&des_ctx, dec_key);
  /* Verify the dec key
     for (i=0; i<96; ++i) {
     if (des_ctx.sk[i] != check_dec_key[i]) {
     print_str("error decrypt des3 key at ");
     print_int(i);
     EOL;
     print_str("should be :"); print_hex_uint(check_dec_key[i]);EOL;
     print_str("value :");print_hex_uint(des_ctx.sk[i]);EOL;
     break;
     }
     }
  */
  /* decrypt */
  memcpy(IV, iv_16, 16);
  des3_crypt_cbc(&des_ctx, DES_DECRYPT, DATA_SIZE, IV, cipher, deciphered);

  /*
   * Verify the message
   */
  if(memcmp(deciphered, plain, DATA_SIZE ) == 0 ) {
    count+=8;
    /*     print_str( "DES encrypt-decrypt OK\n"); */
  } else {
    ++error;
    /*     print_str("DES encrypt-decrypt KO\n"); */
  }
}

void test_md5() {
  md5_context md5_ctx;
  unsigned char hmac1[64], hmac2[64];

  /* Now Compute MD5 on original and deciphered.
   * Should be identical
   */
  memcpy(deciphered, plain, DATA_SIZE);
  md5_starts(&md5_ctx);
  md5_update(&md5_ctx, plain, DATA_SIZE);
  md5_finish(&md5_ctx, hmac1);
  md5_starts(&md5_ctx);
  md5_update(&md5_ctx, deciphered, DATA_SIZE);
  md5_finish(&md5_ctx, hmac2);
  if (memcmp(hmac1, hmac2, 16) == 0) {
    count+=16;
    /*     print_str( "MD5 OK\n"); */
  } else {
    ++error;
    /*     print_str( "MD5 KO\n"); */
  }
}

void test_arc4() {
  arc4_context arc4_ctx;
  unsigned char enc_key[32];

  /* Now Compute ARC4 encryption and decryption */
  memcpy(cipher, plain, DATA_SIZE);
  memcpy(enc_key, key_32, 32);
  arc4_setup(&arc4_ctx, enc_key, 32);
  arc4_crypt(&arc4_ctx, cipher, DATA_SIZE);
  memcpy(enc_key, key_32, 32);
  arc4_setup(&arc4_ctx, enc_key, 32);
  arc4_crypt(&arc4_ctx, cipher, DATA_SIZE);
  if (memcmp(cipher, plain, DATA_SIZE) == 0) {
    count+=32;
    /*     print_str( "ARC4 encrypt OK\n"); */
  } else {
    ++error;
    /*     print_str( "ARC4 encrypt KO\n"); */
  }
}

void test_base64() {
  int b64e_len, b64d_len, err_code;
  /* Now base 64 encryption.
     base64 expands the length, use larger buffer for output
     base64 adds null character at the end. take 2 off */
  b64e_len = BASE64_BUFSIZE;
  if ((err_code=base64_encode(base64_cipher, &b64e_len, plain, DATA_SIZE-2)) == 0) {
    /* print_str("cipher length : "); print_int(b64e_len); EOL; */
  }
  else {
    if (err_code == XYSSL_ERR_BASE64_BUFFER_TOO_SMALL) {
      ++error;
      /*       print_str( "base64 encode buffer too small, should be \n"); */
      /*       print_int(b64e_len); */
      /*       EOL; */
    } else if (err_code == XYSSL_ERR_BASE64_INVALID_CHARACTER) {
      ++error;
      /*       print_str( "base64 decode invalid data\n"); */
    } else {
      ++error;
      /*       print_str( "base64 unknown encode error \n"); */
    }
  }
  b64d_len = DATA_SIZE;
  if ((err_code=base64_decode(deciphered, &b64d_len,
			      base64_cipher, b64e_len)) == 0) {
    /*     print_str("decipher length : "); */
    /*     print_int(b64d_len); EOL; */
  } else if (err_code == XYSSL_ERR_BASE64_BUFFER_TOO_SMALL) {
    ++error;
    /*     print_str( "base64 decode buffer too small: "); */
    /*     print_int(DATA_SIZE); */
    /*     print_str(" should be : "); */
    /*     print_int(b64d_len);  EOL; */
  } else if (err_code ==  XYSSL_ERR_BASE64_INVALID_CHARACTER) {
    ++error;
    /*     print_str( "base64 decode invalid data\n"); */
  } else {
    ++error;
    /*     print_str( "base64 unknown decode error \n"); */
  }
  if (b64d_len != (DATA_SIZE-2)) {
    ++error;
    /*     print_str("base64 does not decrypt to same length"); */
    /*     print_int( DATA_SIZE); */
    /*     print_str(" should be : "); */
    /*     print_int(b64d_len);  EOL; */
  }

  if (memcmp(deciphered, plain, DATA_SIZE) == 0) {
    count+=64;
    /*     print_str( "base64 encrypt OK\n"); */
  } else {
    ++error;
    /*     print_str( "ERROR bas64 encrypt\n"); */
  }
}

void test_rsa() {
  int rsa_len = KEY_SIZE;
  rsa_context rsa_ctx;
  havege_state hs;

  /* Now RSA */
  havege_init(&hs);
  rsa_init(&rsa_ctx, RSA_PKCS_V15, 0, havege_rand, &hs);
  if(rsa_gen_key(&rsa_ctx, KEY_SIZE, EXPONENT ) != 0 ) {
    ++error;
    /*     print_str( "ERROR rsa_gen_key\n"); */
  } else {
    /*     print_str( "rsa_gen_key OK\n"); */
  }
  if (rsa_check_pubkey(&rsa_ctx) != 0) {
    ++error;
    /*     print_str( "ERROR public key\n"); */
  } else {
    /*     print_str( "public key OK\n"); */
  }
  if (rsa_check_privkey(&rsa_ctx) != 0) {
    ++error;
    /*     print_str( "ERROR private key\n"); */
  } else {
    /*     print_str( "private key OK\n"); */
  }
  if (rsa_pkcs1_encrypt(&rsa_ctx, RSA_PUBLIC, 100, plain, cipher ) != 0) {
    ++error;
    /*     print_str( "ERROR rsa encrypt \n"); */
  } else {
    /*     print_str( "rsa encrypt OK \n"); */
  }
  if (rsa_pkcs1_decrypt(&rsa_ctx, RSA_PRIVATE, &rsa_len, cipher, deciphered) != 0) {
    +error;
    /*     print_str( "ERROR rsa decrypt\n"); */
  } else {
    /*     print_str( "rsa decrypt OK \n"); */
  }
  if (memcmp(deciphered, plain, 100) == 0) {
    /*     print_str( "rsa test OK\n"); */
  } else {
    ++error;
    /*     print_str( "ERROR rsa test\n"); */
  }
}

int main()
{
  init_malloc();
  test_malloc();
  /* print_str("crypto start\n"); */
  test_aes();
  test_sha4();
  {
    unsigned char enc_key[32];
    unsigned char dec_key[32];
    test_sha2(enc_key,dec_key);
    test_des(enc_key,dec_key);
  }
  test_md5();
  test_arc4();
  test_base64();
  /*     test_rsa(); */ /* this one is VERY slow */
  return (error<<16)|count;
}
