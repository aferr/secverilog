/*-*-mode:c-*-************************************************************
 *
 *  Copyright (c) 1999 Cornell University
 *  School of Electrical Engineering
 *  Ithaca, NY 14853
 *  All Rights Reserved
 *
 *  Permission to use, copy, modify, and distribute this software
 *  and its documentation for any purpose and without fee is hereby
 *  granted, provided that the above copyright notice appear in all
 *  copies. Cornell University makes no representations
 *  about the suitability of this software for any purpose. It is
 *  provided "as is" without express or implied warranty. Export of this
 *  software outside of the United States of America may require an
 *  export license.
 *
 *  cachecore.c, 2005 July 28 wxl2
 *
 *************************************************************************/
#include "cachecore.h"
#include "vpi_user.h"
#include "misc.h"
CacheLine *GetLines (CacheCore *cc, LL addr)
{
  return &cc->_c[cc->_nsets*((addr & cc->_idxmask) >> cc->_idxsa)];
}

int logbase2 (LL x)
{
  int i = 0;
  LL y;

  y = 1;
  if (y == x) return i;

  for (i=1; x > y; i++) {
    y <<= 1;
    if (y == x) return i;
    if (y == 0) {
      printf ("You're insane\n");
      exit (1);
    }
  }
  return -1;
}

Byte Cache_GetByte (CacheCore *cc, CacheLine *c, LL addr) {
  addr ^= cc->_endianness;
  return c->b[addr & cc->_bytemask];
}

Word Cache_GetHalfWord (CacheCore *cc, CacheLine *c, LL addr) {
  addr ^= cc->_endianness;
  return 0xffff & (*((Word *)&c->b[addr & cc->_hwordmask]));
}
Word Cache_GetWord (CacheCore *cc, CacheLine *c, LL addr) {
  addr ^= cc->_endianness;
  return *((Word *)&c->b[addr & cc->_wordmask]);
}

LL Cache_GetDWord (CacheCore *cc, CacheLine *c, LL addr) {
  addr ^= cc->_endianness;
  return *((LL *)&c->b[addr & cc->_dwordmask]);
}

void Cache_SetByte (CacheCore *cc, CacheLine *c, LL addr, Byte data) {
  addr ^= cc->_endianness;
  c->b[addr & cc->_bytemask] = data;
}

void Cache_SetHalfWord (CacheCore *cc, CacheLine *c, LL addr, Word data) {
  addr ^= cc->_endianness;
#if BYTE_ORDER == BIG_ENDIAN
  c->b[((addr & cc->_bytemask) >> 1) << 1] = data >> 8;
  c->b[1+(((addr & cc->_bytemask) >> 1)<<1)] = data & 0xff;
#else
  c->b[((addr & cc->_bytemask) >> 1)<<1] = data & 0xff;
  c->b[1+(((addr & cc->_bytemask) >> 1)<<1)] = data >> 8;
#endif
}

void Cache_SetWord (CacheCore *cc, CacheLine *c, LL addr, Word data) {
  addr ^= cc->_endianness;
  *((Word*)&c->b[addr & cc->_wordmask]) = data;
}

void Cache_SetDWord (CacheCore *cc, CacheLine *c, LL addr, LL data) {
  addr ^= cc->_endianness;
  *((LL*)&c->b[addr & cc->_dwordmask]) = data;
}

void SetTags (CacheCore *cc, CacheLine *c, LL addr) {
  c->tag = (addr & cc->_tagsmask) >> cc->_lgdata;
  c->valid = 1;
}

// Create a cache data array
CacheCore* new_CacheCore (int nlines, int nbanks, int nsets, int nbytes)
{
  int i, j;
  CacheCore* newcc;
  // generic sanity checks
  Assert (sizeof(Byte) == 1, "Hmm...");
  Assert (sizeof(Word) == 4, "Oh no!");
  Assert (sizeof(LL) == 8, "Yikes");

  newcc = (CacheCore *) malloc(sizeof(CacheCore));
  Assert (newcc, "Bleh!");
  newcc->_nlines = nlines;
  newcc->_nbanks = nbanks;
  newcc->_nlines *= newcc->_nbanks;
  newcc->_nsets = nsets;
  newcc->_nbytes = nbytes;

  // number of doublewords in each cache line
  newcc->nDWords = newcc->_nbytes >> 3;

  newcc->_lgdata = logbase2 (newcc->_nlines*newcc->_nbytes);

  // sanity checks
  if (newcc->_lgdata < 0)
    fatal_error ("All cache parameters must be powers of 2");

  // more sanity checks
  if ((newcc->_nbytes % 8) != 0)
    fatal_error ("A cache line must be a multiple of a double-word (64 bits)");
    
  newcc->_idxmask = (((LL)1 << newcc->_lgdata)-1);
  newcc->_tagsmask = ~newcc->_idxmask;
  newcc->_idxsa = logbase2 (newcc->_nbytes);
  newcc->_banksa = logbase2 (newcc->_nbytes*newcc->_nlines/newcc->_nbanks);

  newcc->_bytemask = (((LL)1 << newcc->_idxsa)-1);
  newcc->_hwordmask = (newcc->_bytemask >> 1) << 1;
  newcc->_wordmask = (newcc->_bytemask >> 2) << 2;
  newcc->_dwordmask = (newcc->_bytemask >> 3) << 3;

#if BYTE_ORDER == BIG_ENDIAN
    // matches local cpu
  newcc->_endianness = 0;
#else
  newcc->_endianness = (newcc->_bytemask) & 0x7;
#endif

  newcc->_c = (CacheLine *)malloc(sizeof(CacheLine)*newcc->_nlines*newcc->_nsets);
  if (!newcc->_c)
    fatal_error ("Malloc failed, size=%d\n", sizeof(CacheLine)*newcc->_nlines*newcc->_nsets);

  // clear the valid bit
  for (i=0; i < newcc->_nlines*newcc->_nsets; i += newcc->_nsets) {
    for (j=0; j < newcc->_nsets; j++) {
      newcc->_c[i+j].valid = 0;
      newcc->_c[i+j].dirty = 0;
      newcc->_c[i+j].way = j;
      //MALLOC (newcc->_c[i+j].b, Byte, newcc->_nbytes);
      newcc->_c[i+j].b = (Byte *) malloc (newcc->_nbytes*sizeof(Byte));
      Assert(newcc->_c[i+j].b,"Uh?!?");
    }
  }
  return newcc;
}

void kill_CacheCore (CacheCore *cc)
{
  int i;
  for (i=0; i < cc->_nlines*cc->_nsets; i++)
    FREE (cc->_c[i].b);
  free (cc->_c);
}

// Hit test
CacheLine *GetLine (CacheCore *cc, LL addr)
{
  CacheLine *cl;
  int i;
  
  cl = GetLines (cc, addr);
  
  for (i=0; i < cc->_nsets; i++) {
     if (cl[i].valid && (cl[i].tag == ((addr & cc->_tagsmask) >> cc->_lgdata)))
      return &cl[i]; // hit
  }
  // miss
  return NULL;
}

