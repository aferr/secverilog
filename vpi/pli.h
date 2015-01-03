/*-*-mode:c-*-************************************************************
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
 *  $Id: pli.h,v 1.2 2006/04/02 05:13:30 kca5 Exp $
 *
 **************************************************************************
 */
#ifndef __PLI_H
#define __PLI_H


#include "syscall.h"

// dll entry points

// returns 32
unsigned int load_mm_size (void);

  // load memory image
void seed_mm (void);

  // load test scripts, skip bootloading
void seed_mm_test (void);

  // loads the next test from the testlist
unsigned int load_next_test (void);

  // load/store to/from memory
unsigned int load_mm (void);
void store_mm (void);

  // print disassembled instruction
void disasm (void);

  // emulate system call
unsigned int emulate_syscall (void);

  // read values of registers after syscall
unsigned int syscall_getreg (void);

  // set values of registers before syscall
void syscall_setreg (void);

  // set value of pc before syscall
void syscall_setpc (void);

  // set value of pc before syscall
unsigned int syscall_getpc (void);

  // print execution rate
void display_rate (void);

  // connect to a remote synchronization server
void sync_setup (void);

  // send register file state to the synchronization server
  // and get back an "ack"
int sync_send (void);

  // end connection
void sync_end (void);

  // create_cache
  //   associativity,  bytes/line, # of lines/set
void create_icache (void);
void create_dcache (void);
void create_scache (void);

// tag access
unsigned int icache_tag_read (void);
void icache_tag_write (void);
unsigned int dcache_tag_read (void);
void dcache_tag_write (void);
unsigned int scache_tag_read (void);
void scache_tag_write (void);

  // data access
unsigned int icache_data_read (void);
void icache_data_write (void);
unsigned int dcache_data_read (void);
void dcache_data_write (void);
unsigned int scache_data_read (void);
void scache_data_write (void);

  // state access
unsigned int icache_state_read (void);
void icache_state_write (void);
unsigned int dcache_state_read (void);
void dcache_state_write (void);
unsigned int scache_state_read (void);
void scache_state_write (void);

//------------------------------------------------------------------------
//
//  system call and backdoor interface
//
//------------------------------------------------------------------------



// MERGE EM
LL GetDWord (LL addr);
Word GetWord (LL addr);

void SetDWord (LL addr, LL data);
void SetWord (LL addr, Word data);

  void SetReg (int reg, LL val);
  LL GetReg (int reg);
  


#endif
