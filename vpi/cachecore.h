#ifndef __CACHECORE_H
#define __CACHECORE_H

#include "mem.h"

typedef struct {
  unsigned int dirty:2;
  unsigned int valid:1;
  unsigned int lru;		// lru bits, enjoy
  int way;			// which way
  LL tag;
  Byte *b;			// data
} CacheLine;

typedef struct {
  int _nbanks;			// # of cache banks
  int _nlines;			// # of cache lines
  int _nsets;			// # of sets
  int _nbytes;			// # of bytes in each cache line
  int nDWords;

  //int nsets; // eh???  why was this here
  
  int _lgdata;			// lg (lines*bytes)
  LL  _tagsmask;		// mask for tags
  LL  _idxmask;			// mask for index
  int _idxsa;			// idx shift amount
  
  int _banksa;			// bank # shift amount
  
  LL  _bytemask;		// mask for byte index
  LL  _hwordmask;		// mask for half-word index
  LL  _wordmask;		// mask for word index
  LL  _dwordmask;		// mask for double-word index
  LL  _endianness;		// xor mask
  
  CacheLine *_c;
} CacheCore;

/*
 * Assumption: a cache line >= sizeof(LL) (LL == DWord)
 *
 * Cache stored in host format, whatever that may be (BIG/LITTLE)
 *
 */

#define DIRTY(c)  (c)->dirty
#define VALID(c)  (c)->valid

CacheCore* new_CacheCore (int nlines, int nbanks, int nsets, int nbytes);
void kill_CacheCore (CacheCore *cc);
CacheLine *GetLines (CacheCore *cc, LL addr);

#define GetLinesFromIndex(cc,index) &(cc->_c[cc->_nsets*index])
#define LineNumber(cc,addr) (int)((addr & cc->_idxmask) >> cc->_idxsa)
#define BankNumber(cc,addr) (int)((addr & cc->_idxmask) >> cc->_banksa)
#define NumBanks(cc) cc->_nbanks
#define NumLines(cc) cc->_nlines
#define NumSets(cc) cc->_nsets
#define GetLineSize(cc) cc->_nbytes
#define HitTest(cc,addr) GetLine(cc, addr) == NULL ? 0 : 1
#define CacheLineStart(cc,addr) (addr & cc->_bytemask) == 0
#define GetBaseAddr(cc,addr) addr & ~cc->_bytemask
#define GetLineAddr(cc,c,addr) (cc->c->tag << cc->_lgdata) | (addr&cc->_idxmask&~cc->_bytemask)
#define GetTagsMask(cc) cc->_tagsmask
#define GetLgData(cc) cc->_lgdata
#define GetByteMask(cc) cc->_bytemask
#define GetIndSA(cc) cc->_idxsa

//  lookup address in cache, check tags. 
//  return NULL if no match, or the cache line if there is a match.

CacheLine *GetLine (CacheCore *cc, LL addr);

// get data corresponding to address in the cache line

Byte Cache_GetByte (CacheCore *cc, CacheLine *c, LL addr);
Word Cache_GetHalfWord (CacheCore *cc, CacheLine *c, LL addr);
Word Cache_GetWord (CacheCore *cc, CacheLine *c, LL addr);
LL Cache_GetDWord (CacheCore *cc, CacheLine *c, LL addr);
void Cache_SetByte (CacheCore *cc, CacheLine *c, LL addr, Byte data);
void Cache_SetHalfWord (CacheCore *cc, CacheLine *c, LL addr, Word data);
void Cache_SetWord (CacheCore *cc, CacheLine *c, LL addr, Word data);
void Cache_SetDWord (CacheCore *cc, CacheLine *c, LL addr, LL data);
void SetTags (CacheCore *cc, CacheLine *c, LL addr);

#endif
