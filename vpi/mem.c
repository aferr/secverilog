/*-*-mode:c++-*-**********************************************************
 *
 *  Copyright (c) 1999 Cornell University
 *  Computer Systems Laboratory
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
 *  $Id: mem.c,v 1.2 2006/04/06 20:07:18 kca5 Exp $
 *
 *************************************************************************/
#include <stdio.h>
#include "mem.h"
#include "misc.h"
#include "vpi_user.h"

#define CHUNK_SIZE 1024		 /*Ocean: 8192*/ 
#define CHUNK_THRESHOLD 16 /* gc threshold */
static int adj_merge_size = CHUNK_SIZE;
#define ADJ_LIMIT CHUNK_SIZE	 /*Ocean*/ 
#define DOUBLE_THRESHOLD (1024*1024*256)


void freemem (Mem *pm)
{
  int i;
  
  if (pm->chunks > 0) {
    for (i=0; i < pm->chunks; i++)
      FREE (pm->mem[i]);
    FREE (pm->mem);
    FREE (pm->mem_len);
    FREE (pm->mem_addr);
    pm->chunks = 0;
    pm->numchunks = 0;
    pm->last_chunk_collect = 0;
  }
}

void kill_Mem (Mem *pm)
{
  freemem(pm);
}

Mem *new_Mem (void)
{
  Mem *newm;

  newm = (Mem *) malloc(sizeof(Mem));
  Assert(newm != NULL, "Wha");

  newm->chunks = 0;
  newm->numchunks = 0;
  newm->last_chunk_collect = 0;

  return newm;
}

/*
 * add one more slot to memory array
 */
void get_more (Mem *pm, int ch, long long num, int merging)
{
  long long newnum;
  unsigned long long t;
  if (num <= 0) return;
  
  if (!merging) {
    Assert ((ch == pm->chunks - 1) ||
	    (pm->mem_len[ch] + num + pm->mem_addr[ch] - 1 < pm->mem_addr[ch+1]),
	    "Overlap violation");

    if (pm->mem_len[ch] < DOUBLE_THRESHOLD)
      newnum = pm->mem_len[ch];
    else 
      newnum = CHUNK_SIZE;

    if (newnum < num)
      newnum = num;

    if (ch < pm->chunks - 1) {
      /* double if possible */
      if (pm->mem_addr[ch] + pm->mem_len[ch] + newnum - 1 < pm->mem_addr[ch+1]) {
	num = newnum;
      }
      else {
	num = pm->mem_addr[ch+1] - pm->mem_addr[ch] - pm->mem_len[ch];
      }
    }
    else {
      num = newnum;
    }
    pm->mem_len[ch] += num;
    REALLOC (pm->mem[ch], LL, pm->mem_len[ch]);
    for (t=pm->mem_len[ch]-1;t>=pm->mem_len[ch]-num;t--) {
      pm->mem[ch][t] = MEM_BAD;
    }
    return;
  }
  /* merging */
  if (pm->mem_len[ch] == 0) {
    pm->mem_len[ch] = num;
    MALLOC (pm->mem[ch], LL, pm->mem_len[ch]);
    for (t=0;t<=pm->mem_len[ch]-1;t++) {
      pm->mem[ch][t] = MEM_BAD;
    }
  }
  else {
    pm->mem_len[ch] += num;
    REALLOC (pm->mem[ch], LL, pm->mem_len[ch]);
    for (t=pm->mem_len[ch]-1;t>=pm->mem_len[ch]-num;t--) {
      pm->mem[ch][t] = MEM_BAD;
    }
  }
}

/*
 * create new chunk, at position "chunks-1"
 *
 * Return values:
 *
 *   1  => created a new chunk at array position "chunks-1"
 *   0  => resized array at position ch
 */
int create_new_chunk (Mem *pm, LL addr, int ch)
{
  int i, gap;
  static int last_create = -1;

  if (pm->chunks == pm->numchunks) {
    if (pm->numchunks == 0) {
      pm->numchunks = 4;
      MALLOC (pm->mem, LL *, pm->numchunks);
      MALLOC (pm->mem_len, LL, pm->numchunks);
      MALLOC (pm->mem_addr, LL, pm->numchunks);
    }
    else {
      pm->numchunks *= 2;
      REALLOC (pm->mem, LL *, pm->numchunks);
      REALLOC (pm->mem_len, LL, pm->numchunks);
      REALLOC (pm->mem_addr, LL, pm->numchunks);
    }
  }
  if (0 <= ch && ch < pm->chunks) {
    /* the new chunk is right next to "ch" */
    if (pm->mem_addr[ch] - addr >= CHUNK_SIZE)
      pm->mem_len[pm->chunks] = CHUNK_SIZE;
    else {
      /* next chunk is close by, we need to just adjust the size of
	 the next chunk by CHUNK_SIZE *backward*
      */
      if (ch > 0) {
	if (last_create == ch) {
	  adj_merge_size *= 2;
	  if (adj_merge_size > ADJ_LIMIT)
	    adj_merge_size = ADJ_LIMIT;
	}
	last_create = ch;
	
	gap = pm->mem_addr[ch] - pm->mem_len[ch-1] - pm->mem_addr[ch-1];
	gap = MIN (gap, adj_merge_size);
	REALLOC (pm->mem[ch], LL, pm->mem_len[ch] + gap);
	for (i=pm->mem_len[ch]-1; i >= 0; i--) {
	  pm->mem[ch][i+gap] = pm->mem[ch][i];
	}
	for (i=0; i < gap; i++) {
	  pm->mem[ch][i] = MEM_BAD;
	}
	pm->mem_addr[ch] = pm->mem_addr[ch] - gap;
	pm->mem_len[ch] = pm->mem_len[ch] + gap;
	return 0;
      }
      pm->mem_len[pm->chunks] = pm->mem_addr[ch] - addr;
    }
    Assert (pm->mem_len[pm->chunks] > 0, "What?");
  }
  else {
    pm->mem_len[pm->chunks] = CHUNK_SIZE;
  }
  MALLOC (pm->mem[pm->chunks], LL, pm->mem_len[pm->chunks]);
  pm->mem_addr[pm->chunks] = 0;
  for (i=0;i<=pm->mem_len[pm->chunks]-1;i++) {
    pm->mem[pm->chunks][i] = MEM_BAD;
  }
  pm->chunks++;
  return 1;
}

int _binsearch (Mem *pm, LL addr)
{
  int i, j, m;
  
  if (pm->chunks == 0) return -1;
  
  i = 0; j = pm->chunks;

  while ((i+1) != j) {
    m = (i+j)/2;
    if (pm->mem_addr[m] > addr)
      j = m;
    else
      i = m;
  }
  if (pm->mem_addr[i] <= addr && addr < pm->mem_addr[i] + pm->mem_len[i])
    return i;
  else {
    return -1;
  }
}



int _binsearchw (Mem *pm, LL addr)
{
  int i, j, m;
  
  if (pm->chunks == 0) return 0;
  
  i = 0; j = pm->chunks;

  // looks like this searches the array from both ends. end result is i becomes the chunk number that holds memory at address addr -- comment by KK - dec 2009
  while ((i+1) != j) {
    m = (i+j)/2;
    if (addr < pm->mem_addr[m])
      j = m;
    else
      i = m;
  }
  if (pm->mem_addr[i] <= addr && addr <= pm->mem_addr[i] + pm->mem_len[i]) {
    if (i > 0 && pm->mem_addr[i-1] + pm->mem_len[i-1] == addr)
      return i-1;
    return i;
  }
  else {
    /* not found */
    if (addr < pm->mem_addr[0])
      return 0;
    else if (addr > pm->mem_addr[pm->chunks-1] + pm->mem_len[pm->chunks-1])
      return pm->chunks;
    else
      return i+1;
  }
}

/*
 * get value @ address addr
 */
LL Read (Mem *pm, LL addr)
{
  int w;
  unsigned long long retVal;


  //printf("sizeLL = %d",sizeof(LL));

  //printf("Read from: %llx\n",addr);

  addr >>= MEM_ALIGN;
  w = _binsearch (pm, addr);
  if (w == -1) {
    retVal = MEM_BAD;
    //    return MEM_BAD;
  }
  else {
    // addr is LL
    // pm is pointer to mem struct
    //
    //vpi_printf("Value: %llx\n", pm->mem[w][addr-pm->mem_addr[w]]);
    retVal = pm->mem[w][addr-pm->mem_addr[w]];
  }
  //printf("retVal = %x\n",retVal);
  return retVal;
}

/* merge two chunks */
void merge_chunks (Mem *pm, int c1, int c2)
{
  unsigned int i;

  Assert (pm->mem_addr[c1]+pm->mem_len[c1] == pm->mem_addr[c2], "What?");
  Assert (c1 < c2, "Hmm...");

  get_more (pm, c1, pm->mem_len[c2], 1);
  for (i=0; i < pm->mem_len[c2]; i++) {
    pm->mem[c1][i+pm->mem_addr[c2]-pm->mem_addr[c1]] = pm->mem[c2][i];
  }
  FREE (pm->mem[c2]);
  for (i=c2; i < pm->chunks-1; i++) {
    pm->mem[i] = pm->mem[i+1];
    pm->mem_len[i] = pm->mem_len[i+1];
    pm->mem_addr[i] = pm->mem_addr[i+1];
  }
  pm->mem_len[i] = 0;
  pm->chunks--;
}

/*
 *  garbage collect chunks periodically
 */
void chunk_gc (Mem *pm, int force)
{
  int i;

  if (force || (pm->chunks - pm->last_chunk_collect > CHUNK_THRESHOLD)) {
    i = 0;
    while (i < pm->chunks-1) {
      if (pm->mem_addr[i]+pm->mem_len[i] == pm->mem_addr[i+1])
	merge_chunks (pm, i, i+1);
      else
	i++;
    }
    pm->last_chunk_collect = pm->chunks;
  }
}


/*
 * store value at addr
 */
void Write (Mem *pm, LL addr, LL val)
{
  int i, j, w;
  int ch, ret;
  LL len;
  LL *data;

  addr >>= MEM_ALIGN;

  w = _binsearchw (pm, addr);
  if (w < pm->chunks &&
      (pm->mem_addr[w] <= addr && addr < pm->mem_addr[w]+pm->mem_len[w])) {
    pm->mem[w][addr-pm->mem_addr[w]] = val;
    return;
  }
  i = w;

  if (i < pm->chunks && pm->chunks > 0 && (addr == pm->mem_addr[i] + pm->mem_len[i])) {
    /* check merging chunks! */
    if (i < pm->chunks-1 && pm->mem_addr[i+1] == addr) {
      /* merge two chunks! */
      merge_chunks (pm,i,i+1);
      pm->mem[i][addr-pm->mem_addr[i]] = val;
      vpi_printf("DEBUG B\n");
      return;
    }
    /* extend chunk! */
    get_more (pm, i, addr-pm->mem_addr[i]-pm->mem_len[i]+1,0);
    pm->mem[i][addr-pm->mem_addr[i]] = val;
    return;
  }
  /* we need to move other chunks to the end */
  ch = i;
  ret = create_new_chunk (pm, addr, ch);
    
  if (ret == 1) {
    /* save data and len */
    data = pm->mem[pm->chunks-1];
    len = pm->mem_len[pm->chunks-1];

    /* move other chunks up */
    for (j = pm->chunks-1; j >= ch+1; j--) {
      pm->mem_addr[j] = pm->mem_addr[j-1];
      pm->mem_len[j] = pm->mem_len[j-1];
      pm->mem[j] = pm->mem[j-1];
    }

    /* set chunk info */
    pm->mem[ch] = data;
    pm->mem_len[ch] = len;
    pm->mem_addr[ch] = addr;

    get_more (pm, ch, addr-pm->mem_addr[ch]-pm->mem_len[ch]+1,0);
    pm->mem[ch][0] = val;
  }
  else if (ret == 0) {
    pm->mem[ch][addr - pm->mem_addr[ch]] = val;
  }
  else {
    fatal_error ("Unknown ret value");
  }

  chunk_gc (pm, 0);
  return;
}

/*
 * read memory image from a file
 */
int ReadImageF (Mem *pm, FILE *fp)
{
  freemem (pm);
  return MergeImageF (pm, fp);
}

/*
 * read memory image from a file
 */
int ReadImageS (Mem *pm, char *s)
{
  FILE *fp;
  int i;

  if (!s) return 0;
  if (!(fp = fopen (s, "r")))
    return 0;
  freemem (pm);
  i = MergeImageF (pm, fp);
  fclose (fp);
  return i;
}

/*
 * read memory image from a file
 */
int MergeImageS (Mem *pm, char *s)
{
  FILE *fp;
  int i;

  if (!s) return 0;
  if (!(fp = fopen (s, "r")))
    return 0;
  i = MergeImageF (pm, fp);
  fclose (fp);

  return i;
}

/*
 * read memory image from a file
 */
int MergeImageF (Mem *pm, FILE *fp)
{

  char buf[1024];
  unsigned int a0,a1,v0,v1;
  unsigned int len;
  LL a, v, tmp;
  int endian;

  while (fgets (buf, 1024, fp)) {
    if (buf[0] == '!') {
      break;
    }
    if (buf[0] == '\n') continue;
    if (buf[0] == '#') continue;
    if (buf[0] == '@') {
      /*
	Format: @address data length:

	 "length" data items starting at "address" all contain
	 "data"
      */
#if MEM_ALIGN == 3
      sscanf (buf+1, "0x%8x%8x 0x%8x%8x %lu", &a0, &a1, &v0, &v1, (long unsigned int *) &len);
      a = ((LL)a0 << 32) | (LL)a1;
      v = ((LL)v0 << 32) | (LL)v1;
#elif MEM_ALIGN == 2
      sscanf (buf+1, "0x%8x 0x%8x %lu", &a, &v, &len);
#else
#error Unknown memory format
#endif
      while (len > 0) {
	Write (pm, a, v);
	a += (1 << MEM_ALIGN);
	len--;
      }
      continue;
    }
    else if (buf[0] == '*') {
      /*
	Format: *address length
	        <list of data>

	 "length" locations starting at "address" contain the data
	 specified in the following "length" lines.
      */
#if MEM_ALIGN == 3
      sscanf (buf+1, "0x%8x%8x %lu", &a0, &a1, (long unsigned int *) &len);
      a = ((LL)a0 << 32) | (LL)a1;
#elif MEM_ALIGN == 2
      sscanf (buf+1, "0x%8x %lu", &a, &len);
#else
#error Unknown memory format
#endif
      while (len > 0 && fgets (buf, 1024, fp)) {
#if MEM_ALIGN == 3
	sscanf (buf, "0x%8x%8x", &v0, &v1);
	v = ((LL)v0 << 32) | (LL)v1;
#elif MEM_ALIGN == 2
	sscanf (buf, "0x%8x", &v);
#else
#error Unknown memory format
#endif
	Write (pm, a, v);
	a += (1 << MEM_ALIGN);
	len--;
      }
      if (len != 0) {
	fatal_error ("Memory format error, *0xaddr len format ends prematurely");
      }
      continue;
    }
    else if (buf[0] == '+' || buf[0] == '-') {
      /* 
	 Handle non-aligned data

	 + or - followed by
	 Format: address length
	         <list of data>

         Starting at address, the following length *bytes* are
	 specified below.

	 Assumptions:
	      length < (1 << MEM_ALIGN)	 
	      +  means big-endian
	      -  means little-endian
      */
      if (buf[0] == '+')
	endian = 1; /* big-endian */
      else
	endian = 0; /* little-endian */
#if MEM_ALIGN == 3
      sscanf (buf+1, "0x%8x%8x %lu", &a0, &a1, (long unsigned int *) &len);
      a = ((LL)a0 << 32) | (LL)a1;
#elif MEM_ALIGN == 2
      sscanf (buf+1, "0x%8x %lu", &a, &len);
#else
#error Unknown memory format
#endif
      while (len > 0 && fgets (buf, 1024, fp)) {
#if MEM_ALIGN == 3
	sscanf (buf, "0x%2x", &v0);
	v = v0;
#elif MEM_ALIGN == 2
	sscanf (buf, "0x%2x", &v);
#else
#error Unknown memory format
#endif
	tmp = Read (pm, a);
	/* write the byte! */
	if (endian) {
	  tmp = (tmp & ~(0xffULL << ((~a & 3)<<3))) | (v << ((~a&3)<<3));
	}
	else {
	  tmp = (tmp & ~(0xffULL << ((a & 3)<<3))) | (v << ((a&3)<<3));
	}
	Write (pm, a, tmp);
	a += 1;
	len--;
      }
      if (len != 0) {
	fatal_error ("Memory format error, *0xaddr len format ends prematurely");
      }
      continue;
    }
#if MEM_ALIGN == 3
    sscanf (buf, "0x%8x%8x 0x%8x%8x", &a0, &a1, &v0, &v1);
    a = ((LL)a0 << 32) | (LL)a1;
    v = ((LL)v0 << 32) | (LL)v1;
#elif MEM_ALIGN == 2
    sscanf (buf, "0x%8x 0x%8x", &a, &v);
#else
#error Unknown memory format
#endif
    Write (pm, a, v);
  }

  a = 0;
  for (a1=0; a1 < pm->chunks; a1++)
    a += pm->mem_len[a1];

  return a;
}

/* Dump memory image */
void DumpImage (Mem *pm, FILE *fp)
{
  int i, j;
  LL addr, data;
  unsigned int len;
  chunk_gc (pm, 1);

  for (i=0; i < pm->chunks; i++) {
    fprintf (fp, "# Chunk %d of %d\n", i, pm->chunks);
    addr = pm->mem_addr[i] << MEM_ALIGN;

    for (j=0; j < pm->mem_len[i]; j++)
      if (pm->mem[i][j] != pm->mem[i][0])
	break;
    if (j == pm->mem_len[i]) {
      data = pm->mem[i][0];
      len = pm->mem_len[i];
#if MEM_ALIGN == 3
      fprintf (fp, "@0x%08x%08x 0x%08x%08x %lu\n",
	       (unsigned int)(addr >> 32),
	       (unsigned int)(addr & 0xffffffff),
	       (unsigned int)(data >> 32),
	       (unsigned int)(data & 0xffffffff), (long unsigned int) len);
#elif MEM_ALIGN == 2
      fprintf (fp, "@0x%08x 0x%08x %lu\n", (unsigned int)addr,
	       (unsigned int) data, len);
#else
#error What?
#endif
    }
    else {
#if MEM_ALIGN == 3
	fprintf (fp, "*0x%08x%08x %lu\n",
		 (unsigned int)(addr >> 32),
		 (unsigned int)(addr & 0xffffffff),
		 (long unsigned int) pm->mem_len[i]);
#elif MEM_ALIGN == 2
	fprintf (fp, "*0x%08x 0x%08x\n", (unsigned int)addr,
		 (unsigned int) pm->mem_len[i]);
#else
#error Unknown mem format
#endif
	for (j=0; j < pm->mem_len[i]; j++) {
	  data = pm->mem[i][j];
#if MEM_ALIGN == 3
	fprintf (fp, "0x%08x%08x\n",
		 (unsigned int)(data >> 32),
		 (unsigned int)(data & 0xffffffff));
#elif MEM_ALIGN == 2
	fprintf (fp, "0x%08x\n", (unsigned int) data);
#else
#error Unknown mem format
#endif
	}
    }
  }
}
