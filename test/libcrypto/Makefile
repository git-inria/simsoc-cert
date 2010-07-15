FILES=aes.c arc4.c base64.c bignum.c des.c havege.c md4.c md5.c rsa.c sha2.c sha4.c
CC=arm-elf-gcc
AR=arm-elf-ar
CFLAGS=-g -O2

all: libcrypto.a

libcrypto.a: $(FILES:%.c=%.o)
	$(AR) crs $@ $^

clean:
	rm -f *.o libcrypto.a
