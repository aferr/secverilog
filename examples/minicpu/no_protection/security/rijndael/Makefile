CC=$(MIPS_HOME)/host-cc.pl -k
#CC=gcc

rijndael: aes.c aes.h aestab.h aesxam.c Makefile
	$(CC) -o rijndael aes.c aesxam.c

clean:
	rm -rf rijndael
