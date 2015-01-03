#ifndef __MEM_H
#define __MEM_H

#include <stdio.h>
#include <stdlib.h>
#include "machine.h"

/*
 * Physical memory: Assumes big-endian format!
 */

#define MEM_BAD  0x0ULL
#define MEM_ALIGN 3 /* bottom three bits zero */

#define MIN(a,b) (((a) < (b)) ? (a) : (b))

typedef unsigned long long  LL; // 64 bits

typedef unsigned char Byte;  // 8 bits

typedef unsigned int Word;  // 32 bits
  
typedef struct {
  int chunks;
  int numchunks;
  int last_chunk_collect;

  // array of blocks of memory
  LL **mem;

  // length of each block
  LL *mem_len;

  // size of each block
  // LL *mem_sz;

  // start address for each block
  LL *mem_addr;

} Mem;

Mem *new_Mem(void);
void kill_Mem(Mem* pm);

int ReadImageS (Mem *pm, char *s);
int ReadImageF (Mem *pm, FILE *fp);	// load fresh memory image
int MergeImageS (Mem *pm, char *s);
int MergeImageF (Mem *pm, FILE *fp);	// merge image from file with current mem
void DumpImage (Mem *pm, FILE *fp);	// write current mem to file
  
LL Read (Mem *pm, LL addr);
void Write (Mem *pm, LL addr, LL val);
  
#define BEReadWord(pm,addr) BEGetWord (addr, Read (pm, addr))    
#define BEWriteWord(pm,addr,val) Write (pm, addr, BESetWord (addr, Read (pm, addr), val))
#define LEReadWord(pm,addr) LEGetWord (addr, Read (pm, addr))
#define LEWriteWord(pm,addr,val) Write (pm, addr, LESetWord (addr, Read (pm, addr), val))
#define BEGetByte(addr,data) (data >> ((~addr & 7)<<3)) & 0xff
#define LEGetByte(addr,data) (data >> ((addr & 7)<<3)) & 0xff
#define BEGetHalfWord(addr,data) (data >> ((~addr & 6)<<3)) & 0xffff
#define LEGetHalfWord(addr, data) (data >> ((addr & 6)<<3)) & 0xffff
#define BEGetWord(addr,data) (data >> ((~addr & 4)<<3)) & 0xffffffff
#define LEGetWord(addr,data) (data >> ((addr & 4)<<3)) & 0xffffffff
#define BESetByte(addr,data,val) ((LL)val<<((~addr & 7)<<3))|(data&~((LL)0xff<<((~addr & 7)<<3)))
#define LESetByte(addr,data,val) {((LL)val<<((addr & 7)<<3))|(data&~((LL)0xff<<((addr & 7)<<3)))
#define BESetHalfWord(addr,data,val) ((LL)val<<((~addr & 6)<<3))|(data&~((LL)0xffff<<((~addr & 6)<<3)))
#define LESetHalfWord(addr,data,val) ((LL)val<<((addr & 6)<<3))|(data&~((LL)0xffff<<((addr & 6)<<3)))
#define BESetWord(addr,data,val) ((LL)val<<((~addr & 4)<<3))|(data&~((LL)0xffffffff<<((~addr & 4)<<3)))
#define LESetWord(addr,data,val) ((LL)val<<((addr & 4)<<3))|(data&~((LL)0xffffffff<<((addr & 4)<<3)))
#define Clear(pm) freemem (pm)

void freemem (Mem *pm);
void get_more (Mem *pm, int chunkid, long long num, int merging);
int  create_new_chunk (Mem *pm, LL addr, int ch);
void merge_chunks (Mem *pm, int chunk1, int chunk2);
void chunk_gc (Mem *pm, int force);
int _binsearch (Mem *pm, LL addr);
int _binsearchw (Mem *pm, LL addr);

#endif
