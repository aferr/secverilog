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
 *  $Id: sys.c,v 1.2 2006/04/06 20:07:18 kca5 Exp $
 *
 *************************************************************************/

#include "pli.h"
#include "vpi_user.h"
#include "cachecore.h"
#include "misc.h"

SysCall *syscall_iface;
extern CacheCore *Dcache;
extern Mem *physical_memory;

LL GetDWord (LL addr)
{
   LL xx;
  if (!physical_memory)
    physical_memory = new_Mem();
  if (Dcache) {
    CacheLine *c;
    
    if ((c = GetLine (Dcache, addr))) {
      xx = Cache_GetDWord (Dcache, c, addr);
      //       printf ("LHit: %qx %qx\n", addr, xx);
      return xx;
    }
  }
  xx = Read (physical_memory, addr);
  //  printf ("LMiss: %qx %qx\n", addr, xx);
  //return Read (physical_memory, addr);
  return xx;
}

void SetDWord (LL addr, LL data)
{
  if (!physical_memory)
    physical_memory = new_Mem();
  if (Dcache) {
    CacheLine *c;
    if ((c = GetLine (Dcache, addr))) {
      Cache_SetDWord (Dcache, c, addr, data);
    }
  }
  Write (physical_memory, addr, data);
}

Word GetWord (LL addr)
{
   Word xx;

  if (!physical_memory)
    physical_memory = new_Mem();

  if (Dcache) {
    CacheLine *c;

    if ((c = GetLine (Dcache, addr))) {
      xx = Cache_GetWord (Dcache, c, addr);
      //       printf ("Hit: %qx %x\n", addr, xx);
      return xx;
    }
  }
  xx = BEReadWord (physical_memory, addr);
  //  printf ("Miss: %qx %x\n", addr, xx);
  return xx;
}

void SetWord (LL addr, Word data)
{
  if (!physical_memory)
    physical_memory = new_Mem();

  if (Dcache) {
    CacheLine *c;
    if ((c = GetLine (Dcache, addr))) {
      Cache_SetWord (Dcache, c, addr, data);
    }
  }

  BEWriteWord (physical_memory, addr, data);
}

// Regs

void SetReg (int reg, LL val)
{
  //vpi_printf("SetReg [%d] to %08x\n",reg,val);
  if(!syscall_iface) {
    syscall_iface = new_SysCall();
  }
  
  syscall_iface->_reg[reg] = (Word)val;
}


LL GetReg (int reg)
{
  if(!syscall_iface) {
    //vpi_printf("No syscall_iface defined, creating new syscall_iface\n");
    syscall_iface = new_SysCall();
  }
  //vpi_printf("GetReg[%i]: Value: %08x\n",reg,syscall_iface->_reg[reg]);
  return syscall_iface->_reg[reg];
}

unsigned int emulate_syscall (void)
{
  //printf("I have received an emulate syscall PLI thing\n");
  if (vpi_nargs() != 0) {
   fatal_error ("Error -- wrong args to emulate syscall!\n");
  }
  // Create syscall interface upon first use
  if(!syscall_iface) {
    //vpi_printf("Creating syscall_iface\n");
    syscall_iface = new_SysCall();
  }
    
  EmulateSysCall (syscall_iface);
  if (syscall_iface->quit) {
    vpi_set_retval(0,1); //return 1;
  }
  else {
    vpi_set_retval(0,0); //return 0;
  }
  return 0; // dummy value ss868
}


unsigned int syscall_getreg (void)
{
  if (vpi_nargs() != 1) {
   vpi_printf ("Error -- getreg needs one argument\n");
    return 0;
  }
  //vpi_printf("GetReg[%i] from emulator. Value: %08x\n",vpi_getarg_int(1),GetReg(vpi_getarg_int(1)));
  vpi_set_retval(0,GetReg(vpi_getarg_int(1)));
  //return GetReg (vpi_getarg_int(1));
  return 0; // dummy value ss868
}

void syscall_setreg (void)
{
  if (vpi_nargs() != 2) {
    fatal_error ("Error -- setreg needs two arguments\n");
    return;
  }
  //vpi_printf("Setting emulator reg[%d] to %08x\n",vpi_getarg_int(1),vpi_getarg_int(2));
  SetReg (vpi_getarg_int(1), vpi_getarg_int(2));
}

void syscall_setpc (void)
{
  if (vpi_nargs () != 1) {
    fatal_error ("Error -- setpc needs one argument\n");
    return;
  }

  if(!syscall_iface) {
    syscall_iface = new_SysCall();
  }

  //vpi_printf("Setting emulator PC to %08x\n",vpi_getarg_int(1));
  syscall_iface->pc = vpi_getarg_int (1);
}

/* FIXME! */
unsigned int syscall_getpc (void)
{
  if (vpi_nargs () != 0) {
   vpi_printf ("Error -- getpc no arguments\n");
    return 0;
  }

  if(!syscall_iface) {
    syscall_iface = new_SysCall();
  }


  return syscall_iface->pc;
}
