/*************************************************************************
 *
 *  Copyright (c) 1999 Cornell University
 *  Computer Systems Laboratory
 *  Cornell University, Ithaca, NY 14853
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
 *  vcache.c, 2005 July 28 wxl2
 *
 **************************************************************************
 */

#include "cachecore.h"
#include "vpi_user.h"
#include "misc.h"
//#include "veriuser.h"
CacheCore *Icache = NULL;
CacheCore *Dcache = NULL;
CacheCore *Scache = NULL;

// I$

void create_icache ()
{
  if (Icache) {
    printf ("How many Icaches do you want, BTW?\n");
    return;
  }
  if (vpi_nargs() != 3) {
    fatal_error ("Usage: create_cache #sets linesize #lines/set");
  }

  Icache = new_CacheCore (vpi_getarg_int (3), 1, vpi_getarg_int (1), vpi_getarg_int
		     (2));
  if (!Icache) {
    fatal_error ("Could not create cache core!");
  }
}

unsigned int icache_tag_read ()
{
  if (!Icache) {
    fatal_error ("You need to create an I cache before accessing it...");
  }
  if (vpi_nargs() != 2) {
    fatal_error ("Usage: icache_tag_read index set#");
  }

  unsigned int index, set;

  index = vpi_getarg_int(1);
  set = vpi_getarg_int(2);

  if (index >= NumLines(Icache)) {
    fatal_error ("Specified index 0x%x is out of range", index);
  }
  if (set >= NumSets(Icache)) {
    fatal_error ("Specified set number %d is out of range", set);
  }
  //vpi_printf("icache_tag_read(index: 0x%x set: %d)\n",index,set);
  CacheLine *c = GetLinesFromIndex (Icache, index);
  //vpi_printf("Returning: 0x%x\n",(unsigned int)c[set].tag);
  vpi_set_retval(0,(unsigned int)c[set].tag);
  //return (unsigned int)c[set].tag;
  return 0; // dummy value ss868
}

unsigned int icache_state_read ()
{
  if (!Icache) {
    fatal_error ("You need to create an I cache before accessing it...");
  }
  if (vpi_nargs() != 2) {
    fatal_error ("Usage: icache_state_read index set#");
  }

  unsigned int index, set;

  index = vpi_getarg_int(1);
  set = vpi_getarg_int(2);

  if (index >= NumLines(Icache)) {
    fatal_error ("Specified index 0x%x is out of range", index);
  }
  if (set >= NumSets(Icache)) {
    fatal_error ("Specified set number %d is out of range", set);
  }
  //vpi_printf("icache_state_read(index: 0x%x set: %d)\n",index,set);
  CacheLine *c = GetLinesFromIndex (Icache, index);
  //vpi_printf("Returning: %d\n",(c[set].valid | ((c[set].dirty&1) << 1) | (c[set].lru << 2)));
  vpi_set_retval(0,c[set].valid | ((c[set].dirty&1) << 1) | (c[set].lru << 2));
  //return c[set].valid | ((c[set].dirty&1) << 1) | (c[set].lru << 2);
  return 0; // dummy value ss868
}


void icache_tag_write ()
{
  if (!Icache) {
    fatal_error ("You need to create an I cache before accessing it...");
  }
  if (vpi_nargs() != 3) {
    fatal_error ("Usage: icache_tag_write index set# value");
  }

  unsigned int index, set, tag;

  index = vpi_getarg_int(1);
  set = vpi_getarg_int(2);
  tag = vpi_getarg_int(3);

  if (index >= NumLines(Icache)) {
    fatal_error ("Specified index 0x%x is out of range", index);
  }
  if (set >= NumSets(Icache)) {
    fatal_error ("Specified set number %d is out of range", set);
  }
  //vpi_printf("icache_tag_write(index: 0x%x set: %d tag: 0x%x)\n",index,set,tag);
  CacheLine *c = GetLinesFromIndex (Icache, index);

  c[set].tag = tag;
}

void icache_state_write ()
{
  if (!Icache) {
    fatal_error ("You need to create an I cache before accessing it...");
  }
  if (vpi_nargs() != 3) {
    fatal_error ("Usage: icache_state_write index set# value");
  }

  unsigned int index, set, value;

  index = vpi_getarg_int(1);
  set = vpi_getarg_int(2);
  value = vpi_getarg_int(3);

  if (index >= NumLines(Icache)) {
    fatal_error ("Specified index 0x%x is out of range", index);
  }
  if (set >= NumSets(Icache)) {
    fatal_error ("Specified set number %d is out of range", set);
  }
  //vpi_printf("icache_state_write(index: 0x%x set: %d value: 0x%x)\n",index,set,value);
  CacheLine *c = GetLinesFromIndex (Icache, index);

  c[set].valid = value & 1;
  c[set].dirty = (value >> 1) & 1;
  c[set].lru = value >> 2;
}



unsigned int icache_data_read ()
{
  if (!Icache) {
    fatal_error ("You need to create an I cache before accessing it...");
  }

  if (vpi_nargs() != 3) {
    fatal_error ("Usage: icache_data_read index set# offset");
  }

  unsigned int index, set, offset;

  index = vpi_getarg_int(1);
  set = vpi_getarg_int(2);
  offset = vpi_getarg_int(3);

  if (index >= NumLines(Icache)) {
    fatal_error ("Specified index 0x%x is out of range", index);
  }
  if (set >= NumSets(Icache)) {
    fatal_error ("Specified set number %d is out of range", set);
  }
  if (offset >= Icache->nDWords*2) {
    fatal_error ("Specified offset %d is out of range", offset);
  }
  CacheLine *c = GetLinesFromIndex (Icache, index);
  //vpi_printf("icache_data_read(index: 0x%x set: %d offset: %d)\n",index,set,offset);
  //vpi_printf("Returning: %x\n",(Cache_GetWord(Icache,c+set,offset << 2)));
  vpi_set_retval(0,Cache_GetWord (Icache, c+set, offset << 2));
  //return Cache_GetWord (Icache, c+set, offset << 2);
  return 0; // dummy value ss868
}

void icache_data_write ()
{
  if (!Icache) {
    fatal_error ("You need to create an I cache before accessing it...");
  }

  if (vpi_nargs() != 4) {
    fatal_error ("Usage: icache_data_write index set# offset data");
  }

  unsigned int index, set, offset, value;

  index = vpi_getarg_int(1);
  set = vpi_getarg_int(2);
  offset = vpi_getarg_int(3);
  value = vpi_getarg_int(4);

  if (index >= NumLines(Icache)) {
    fatal_error ("Specified index 0x%x is out of range", index);
  }
  if (set >= NumSets(Icache)) {
    fatal_error ("Specified set number %d is out of range", set);
  }
  if (offset >= Icache->nDWords*2) {
    fatal_error ("Specified offset %d is out of range", offset);
  }
  CacheLine *c = GetLinesFromIndex (Icache, index);
  //vpi_printf("icache_data_write(index: 0x%x set: %d offset: %d value: 0x%x)\n",index,set,offset,value);
  Cache_SetWord (Icache, c+set, offset << 2, value);
}

// D$

void create_dcache ()
{
  if (Dcache) {
    printf ("How many Dcaches do you want, BTW?\n");
    return;
  }
  if (vpi_nargs() != 3) {
    fatal_error ("Usage: create_cache #sets linesize #lines/set");
  }

  Dcache = new_CacheCore (vpi_getarg_int (3), 1, vpi_getarg_int (1), vpi_getarg_int
		     (2));
  if (!Dcache) {
    fatal_error ("Could not create cache core!");
  }
}

unsigned int dcache_tag_read ()
{
  if (!Dcache) {
    fatal_error ("You need to create a data cache before accessing it...");
  }
  if (vpi_nargs() != 2) {
    fatal_error ("Usage: dcache_tag_read index set#");
  }

  unsigned int index, set;

  index = vpi_getarg_int(1);
  set = vpi_getarg_int(2);

  if (index >= NumLines(Dcache)) {
    fatal_error ("Specified index 0x%x is out of range", index);
  }
  if (set >= NumSets(Dcache)) {
    fatal_error ("Specified set number %d is out of range", set);
  }

  CacheLine *c = GetLinesFromIndex (Dcache, index);
  //vpi_printf("dcache_tag_read(index: 0x%x set: %d)\n",index,set);
  vpi_set_retval(0,(unsigned int) c[set].tag);
  //return (unsigned int)c[set].tag;
  return 0; // dummy value ss868
}

unsigned int dcache_state_read ()
{
  if (!Dcache) {
    fatal_error ("You need to create a data cache before accessing it...");
  }
  if (vpi_nargs() != 2) {
    fatal_error ("Usage: dcache_state_read index set#");
  }

  unsigned int index, set;

  index = vpi_getarg_int(1);
  set = vpi_getarg_int(2);

  if (index >= NumLines(Dcache)) {
    fatal_error ("Specified index 0x%x is out of range", index);
  }
  if (set >= NumSets(Dcache)) {
    fatal_error ("Specified set number %d is out of range", set);
  }
  CacheLine *c = GetLinesFromIndex (Dcache, index);
  //vpi_printf("dcache_state_read(index: 0x%x set: %d)\n",index,set);
  vpi_set_retval(0,c[set].valid | ((c[set].dirty&1) << 1) | (c[set].lru << 2));
  //return c[set].valid | ((c[set].dirty&1) << 1) | (c[set].lru << 2);
  return 0; // dummy value ss868
}


void dcache_tag_write ()
{
  if (!Dcache) {
    fatal_error ("You need to create a data cache before accessing it...");
  }
  if (vpi_nargs() != 3) {
    fatal_error ("Usage: dcache_tag_write index set# value");
  }

  unsigned int index, set, tag;

  index = vpi_getarg_int(1);
  set = vpi_getarg_int(2);
  tag = vpi_getarg_int(3);

  if (index >= NumLines(Dcache)) {
    fatal_error ("Specified index 0x%x is out of range", index);
  }
  if (set >= NumSets(Dcache)) {
    fatal_error ("Specified set number %d is out of range", set);
  }
  //vpi_printf("dcache_tag_write(index: 0x%x set: %d tag: 0x%x)\n",index,set,tag);
  CacheLine *c = GetLinesFromIndex (Dcache, index);

  c[set].tag = tag;
}

void dcache_state_write ()
{
  if (!Dcache) {
    fatal_error ("You need to create a data cache before accessing it...");
  }

  if (vpi_nargs() != 3) {
    fatal_error ("Usage: dcache_state_write index set# value");
  }

  unsigned int index, set, value;

  index = vpi_getarg_int(1);
  set = vpi_getarg_int(2);
  value = vpi_getarg_int(3);

  if (index >= NumLines(Dcache)) {
    fatal_error ("Specified index 0x%x is out of range", index);
  }
  if (set >= NumSets(Dcache)) {
    fatal_error ("Specified set number %d is out of range", set);
  }
  CacheLine *c = GetLinesFromIndex (Dcache, index);
  //vpi_printf("dcache_state_write(index: 0x%x set: %d value:%x\n",index,set,value);
  c[set].valid = value & 1;
  c[set].dirty = (value >> 1) & 1;
  c[set].lru = value >> 2;
}



unsigned int dcache_data_read ()
{
  if (!Dcache) {
    fatal_error ("You need to create a data cache before accessing it...");
  }

  if (vpi_nargs() != 3) {
    fatal_error ("Usage: dcache_data_read index set# offset");
  }

  unsigned int index, set, offset;

  index = vpi_getarg_int(1);
  set = vpi_getarg_int(2);
  offset = vpi_getarg_int(3);

  if (index >= NumLines(Dcache)) {
    fatal_error ("Specified index 0x%x is out of range", index);
  }
  if (set >= NumSets(Dcache)) {
    fatal_error ("Specified set number %d is out of range", set);
  }
  if (offset >= Dcache->nDWords*2) {
    fatal_error ("Specified offset %d is out of range", offset);
  }
  CacheLine *c = GetLinesFromIndex (Dcache, index);
  //vpi_printf("dcache_data_read(index: 0x%x set: %d offset: %d)\n",index,set,offset);
  //vpi_printf("Returning: 0x%x\n",Cache_GetWord(Dcache,c+set,offset <<2));
  vpi_set_retval(0,Cache_GetWord (Dcache, c+set, offset << 2));
  //return Cache_GetWord (Dcache, c+set, offset << 2);
  return 0; // dummy value ss868
}

void dcache_data_write ()
{
  if (!Dcache) {
    fatal_error ("You need to create a data cache before accessing it...");
  }

  if (vpi_nargs() != 4) {
    fatal_error ("Usage: dcache_data_write index set# offset data");
  }


  unsigned int index, set, offset, value;

  index = vpi_getarg_int(1);
  set = vpi_getarg_int(2);
  offset = vpi_getarg_int(3);
  value = vpi_getarg_int(4);

  if (index >= NumLines(Dcache)) {
    fatal_error ("Specified index 0x%x is out of range", index);
  }
  if (set >= NumSets(Dcache)) {
    fatal_error ("Specified set number %d is out of range", set);
  }
  if (offset >= Dcache->nDWords*2) {
    fatal_error ("Specified offset %d is out of range", offset);
  }
  CacheLine *c = GetLinesFromIndex (Dcache, index);
  //vpi_printf("dcache_data_write(index: 0x%x set: %d offset: %d value: 0x%x)\n",index,set,offset,value);
  Cache_SetWord (Dcache, c+set, offset << 2, value);
}


// S$

void create_scache ()
{
  if (Scache) {
    printf ("How many Scaches do you want, BTW?\n");
    return;
  }
  if (vpi_nargs() != 3) {
    fatal_error ("Usage: create_cache #sets linesize #lines/set");
  }

  Scache = new_CacheCore (vpi_getarg_int (3), 1, vpi_getarg_int (1), vpi_getarg_int
		     (2));
  if (!Scache) {
    fatal_error ("Could not create cache core!");
  }
}

unsigned int scache_tag_read ()
{
  if (!Scache) {
    fatal_error ("You need to create a Scache before accessing it...");
  }
  if (vpi_nargs() != 2) {
    fatal_error ("Usage: scache_tag_read index set#");
  }

  unsigned int index, set;

  index = vpi_getarg_int(1);
  set = vpi_getarg_int(2);

  if (index >= NumLines(Scache)) {
    fatal_error ("Specified index 0x%x is out of range", index);
  }
  if (set >= NumSets(Scache)) {
    fatal_error ("Specified set number %d is out of range", set);
  }

  CacheLine *c = GetLinesFromIndex (Scache, index);
  vpi_set_retval(0,(unsigned int)c[set].tag);
  //return (unsigned int)c[set].tag;
  return 0; // dummy value ss868
}

unsigned int scache_state_read ()
{
  if (!Scache) {
    fatal_error ("You need to create a Scache before accessing it...");
  }
  if (vpi_nargs() != 2) {
    fatal_error ("Usage: scache_state_read index set#");
  }

  unsigned int index, set;

  index = vpi_getarg_int(1);
  set = vpi_getarg_int(2);

  if (index >= NumLines(Scache)) {
    fatal_error ("Specified index 0x%x is out of range", index);
  }
  if (set >= NumSets(Scache)) {
    fatal_error ("Specified set number %d is out of range", set);
  }
  CacheLine *c = GetLinesFromIndex (Scache, index);
  vpi_set_retval(0,c[set].valid | ((c[set].dirty&1) << 1) | (c[set].lru << 2));
  //return c[set].valid | ((c[set].dirty&1) << 1) | (c[set].lru << 2);
  return 0; // dummy value ss868
}


void scache_tag_write ()
{
  if (!Scache) {
    fatal_error ("You need to create a Scache before accessing it...");
  }
  if (vpi_nargs() != 3) {
    fatal_error ("Usage: scache_tag_write index set# value");
  }

  unsigned int index, set, tag;

  index = vpi_getarg_int(1);
  set = vpi_getarg_int(2);
  tag = vpi_getarg_int(3);

  if (index >= NumLines(Scache)) {
    fatal_error ("Specified index 0x%x is out of range", index);
  }
  if (set >= NumSets(Scache)) {
    fatal_error ("Specified set number %d is out of range", set);
  }
  
  CacheLine *c = GetLinesFromIndex (Scache, index);

  c[set].tag = tag;
}

void scache_state_write ()
{
  if (!Scache) {
    fatal_error ("You need to create a Scache before accessing it...");
  }
  if (vpi_nargs() != 3) {
    fatal_error ("Usage: scache_state_write index set# value");
  }

  unsigned int index, set, value;

  index = vpi_getarg_int(1);
  set = vpi_getarg_int(2);
  value = vpi_getarg_int(3);

  if (index >= NumLines(Scache)) {
    fatal_error ("Specified index 0x%x is out of range", index);
  }
  if (set >= NumSets(Scache)) {
    fatal_error ("Specified set number %d is out of range", set);
  }
  
  CacheLine *c = GetLinesFromIndex (Scache, index);

  c[set].valid = value & 1;
  c[set].dirty = (value >> 1) & 1;
  c[set].lru = value >> 2;
}



unsigned int scache_data_read ()
{
  if (!Scache) {
    fatal_error ("You need to create a Scache before accessing it...");
  }

  if (vpi_nargs() != 3) {
    fatal_error ("Usage: scache_data_read index set# offset");
  }

  unsigned int index, set, offset;

  index = vpi_getarg_int(1);
  set = vpi_getarg_int(2);
  offset = vpi_getarg_int(3);

  if (index >= NumLines(Scache)) {
    fatal_error ("Specified index 0x%x is out of range", index);
  }
  if (set >= NumSets(Scache)) {
    fatal_error ("Specified set number %d is out of range", set);
  }
  if (offset >= Scache->nDWords*2) {
    fatal_error ("Specified offset %d is out of range", offset);
  }
  CacheLine *c = GetLinesFromIndex (Scache, index);
  vpi_set_retval(0,Cache_GetWord (Scache, c+set, offset << 2));
  //return Cache_GetWord (Scache, c+set, offset << 2);
  return 0; // dummy value ss868
}

void scache_data_write ()
{
  if (!Scache) {
    fatal_error ("You need to create a Scache before accessing it...");
  }

  if (vpi_nargs() != 4) {
    fatal_error ("Usage: scache_data_write index set# offset data");
  }

  unsigned int index, set, offset, value;

  index = vpi_getarg_int(1);
  set = vpi_getarg_int(2);
  offset = vpi_getarg_int(3);
  value = vpi_getarg_int(4);

  if (index >= NumLines(Scache)) {
    fatal_error ("Specified index 0x%x is out of range", index);
  }
  if (set >= NumSets(Scache)) {
    fatal_error ("Specified set number %d is out of range", set);
  }
  if (offset >= Scache->nDWords*2) {
    fatal_error ("Specified offset %d is out of range", offset);
  }
  CacheLine *c = GetLinesFromIndex (Scache, index);

  Cache_SetWord (Scache, c+set, offset << 2, value);
}


