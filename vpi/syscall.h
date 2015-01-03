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
 *  $Id: syscall.h,v 1.1 2006/04/02 05:00:08 kca5 Exp $
 *
 *************************************************************************/

#ifndef __SYSCALL_H
#define __SYSCALL_H

#include "mem.h"
//#include "app_syscall.h"

#define REG_V0 2
#define REG_V1 3

#define REG_A0 4
#define REG_A1 5
#define REG_A2 6
#define REG_A3 7
#define REG_T0 8
#define REG_T1 9

#define REG_GP 28
#define REG_SP 29

typedef struct {
  
  int quit;
  
  LL pc;

  LL _num_load;
  LL _num_store;
  LL _num_load_since_reset;
  LL _num_store_since_reset;

  Mem *m;
  int _fdlist[256];

  int _argc;
  char **_argv;
  LL _argaddr;

  // from MySysCall
  Word _reg[32];
  Word _pc;
} SysCall;

//class Mipc;

SysCall *new_SysCall (void);
//SysCall (Mipc *ms);
void kill_SysCall (SysCall *sc);

void Reset (SysCall *sc);

  /* 
   * Call this for argument setup backdoor call
   *
   *   - argc, argv : arguments
   *   - addr       : address in simulated memory where the
   *                  argv array can be stored.
   *
   */
void ArgumentSetup (SysCall *sc, int argc, char **argv, LL addr);

// help?
/*virtual LL GetDWord (LL addr) = 0;
virtual void SetDWord (LL addr, LL value) = 0;

virtual Word GetWord (LL addr) = 0;
virtual void SetWord (LL addr, Word value) = 0;
  
virtual void SetReg (int regnum, LL value) = 0;
virtual LL   GetReg (int regnum) = 0;*/


LL GetDWord (LL addr);
void SetDWord (LL addr, LL value);
Word GetWord (LL addr);
void SetWord (LL addr, Word value);
void SetReg (int regnum, LL value);
LL   GetReg (int regnum);

void WriteByte (LL addr, unsigned char byte);
unsigned char ReadByte (LL addr);
void WriteWord (LL addr, Word w);
Word ReadWord (LL addr);
void WriteHalf (LL addr, Word w);
Word ReadHalf (LL addr);

// help?
void EmulateSysCall (SysCall *sc);
void PrintError (char *s, ...);

#define GetTime(void) 0
#define GetCpuId(void) 0

#define CreateCall(x,y) while(0)	//Must be overridden
#define WaitCall(x) while(0)	//Must be overridden
#define ResetCall(x) while(0)	//Must be overridden
#define PlaceRangeCall(x,y,z) while(0) //Must be overridden

LL _emulate_fxstat (int fd, LL addr);
LL _emulate_gettime(LL ts_addr, LL tz_addr);
char *SysCallName (int num);

#endif
