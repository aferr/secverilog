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
 *  $Id: dis.c,v 1.6 2006/04/09 02:12:55 kca5 Exp $
 *
 *************************************************************************/
#include "opcodes.h"
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include "dis.h"
#include "vpi_user.h"

/* Symbolic register names. */
static char *regname[] = {
  "0",  "at", "v0", "v1", "a0", "a1", "a2", "a3",
  "t0", "t1", "t2", "t3", "t4", "t5", "t6", "t7",
  "s0", "s1", "s2", "s3", "s4", "s5", "s6", "s7",
  "t8", "t9", "k0", "k1", "gp", "sp", "s8", "ra"
};

/**
 * Append the name of a register to the string.
 * @param s the string to append to
 * @param type DIS_TYPE_NUMBER to use register numbers, else use
 *  symbolic register names.
 * @param num the register number to append
 */
static void sprintreg (char *s, int type, int num)
{
  char tmp[10];
  
  if (type == DIS_TYPE_NUMBER) {
    sprintf (tmp, "$%d", num);
  }
  else {
    sprintf (tmp, "$%s", regname[num]);
  }
  strcat (s, tmp);
}

/**
 * Append a floating-point register (always numeric)
 * @param s the string to append to
 * @param type ignored; numeric registers are always used.
 * @param num the register number to append
 */
static void fpsprintreg (char *s, int type, int num)
{
  char tmp[10];

  sprintf (tmp, "$f%d", num);
  strcat (s, tmp);
}

/**
 * FIXME: document.
 */
char getfmt(MipsInsn mi)
{
    switch (mi.freg.fmt) {
    case 0x10: return 's';
    case 0x11: return 'd';
    case 0x14: return 'w';
    default:   return 'x';
    }
}

/**
 * Sign-extends a 16-bit number to the width of an int.
 * @param the 16-bit number to extend (MUST be less than 2^16)
 * @return the sign-extended result, usable as a C integer.
 */ 
signed int sext_16(unsigned int x)
{
  if (x&0x8000) {
    // Negative. Replace the bottom 16 bits of -1 with x.
    signed int ret = -1;
    ret &= ~0xffff;
    ret |= x;
    return ret;
  } else
    return x;
}

/**
 * Disassemble a MIPS instruction
 * @param type DIS_TYPE_NUMBER to use register numbers, else use
 *  symbolic register names.
 * @param ins the instruction to disassemble.
 * @return the disassembled instruction, stored in a static character buffer.
 *  Previous returned results are invalidated after calling this again.
 */
char *mips_dis_insn (int type, unsigned int ins)
{
  static char buf[128];
  char tmp[32];
  MipsInsn mi;

  mi.data = ins;

  if (mi.data == 0) {
    sprintf (buf, "[%08x] nop", 0);
    return buf;
  }

#define OUTPUT(en,str,op,flags)				\
     case op:						\
      sprintf (buf, "[%08x] %s\t", mi.data, str);

#define FPOUTPUT(en,str,op,flags)			\
     case op:						\
       if (USE_FMT(flags)) {				\
         sprintf (buf, "[%08x] %s.%c\t", mi.data, str, getfmt(mi)); \
       }						\
       else if ((flags) & P_BRANCH) {				\
         sprintf (buf, "[%08x] %s%c\t", mi.data, str, (mi.freg.ft==0x1)?'t':'f');\
       }						\
       else						\
         sprintf (buf, "[%08x] %s\t", mi.data, str);	

  switch (mi.reg.op) {
  case 0x0:
    switch (mi.reg.func) {

#define SPECIAL(en,str,op,flags)		\
	OUTPUT(en,str,op,flags);		\
	if (USE_RD(flags)) {			\
	  sprintreg (buf, type, mi.reg.rd);	\
	  strcat (buf, ",");			\
	}					\
	if (USE_RS(flags)) {			\
	  sprintreg (buf, type, mi.reg.rs);	\
          if (USE_RT(flags))			\
	  strcat (buf, ",");			\
	}					\
	if (USE_RT(flags)){			\
	  sprintreg (buf, type, mi.reg.rt);	\
	  if (!USE_RS (flags)) {		\
	    sprintf (tmp, ",%d", mi.reg.sa);	\
	    strcat (buf, tmp);			\
	  }					\
	}					\
	break;

#include "opcodes.def"

    default:
      sprintf (buf, "[%08x] unknown special", mi.data);
      break;
    }
    break;

  case 0x11:
    switch (mi.freg.fmt) {			

#define COP1CTL(en,str,op,flags)		\
	FPOUTPUT(en,str,op,flags);		\
	if (USE_RT(flags)) {			\
	  fpsprintreg (buf, type, mi.freg.ft);	\
          if (USE_RS(flags))			\
	  strcat (buf, ",");			\
	}					\
	if (USE_RS(flags)){			\
	  fpsprintreg (buf, type, mi.freg.fs);	\
	}					\
	break;

#include "opcodes.def"

    default:					
      switch (mi.freg.func) {			

#define COP1FCN(en,str,op,flags)		\
	FPOUTPUT(en,str,op,flags);		\
	if (USE_RD(flags)) {			\
	  fpsprintreg (buf, type, mi.freg.fd);	\
	  strcat (buf, ",");			\
	}					\
	if (USE_RS(flags)) {			\
	  fpsprintreg (buf, type, mi.freg.fs);	\
          if (USE_RT(flags))			\
	  strcat (buf, ",");			\
	}					\
	if (USE_RT(flags)){			\
	  fpsprintreg (buf, type, mi.freg.ft);	\
	}					\
	break;

#include "opcodes.def"

      default:
        sprintf (buf, "[%08x] unknown fpu", mi.data);
        break;
      }
    }
    break;

  case 0x1:
    switch (mi.reg.rt) {

#define REGIMM(en,str,op,flags)				\
	OUTPUT(en,str,op,flags);			\
	if (USE_RS(flags)) {				\
	  sprintreg (buf, type, mi.imm.rs);		\
	  strcat (buf, ",");				\
	}						\
	sprintf (tmp, "%d", 4*sext_16(mi.imm.imm));	\
        strcat (buf, tmp);				\
	break;
	
#include "opcodes.def"

    default:
      sprintf (buf, "[%08x] unknown regimm", mi.data);
      break;
    }
    break;
  
#define MAINOP(en,str,op,flags)					\
      OUTPUT(en,str,op,flags);					\
      if (JUMPIMM(flags)) {					\
	int offset = mi.tgt.tgt;				\
	offset <<= 2;						\
	sprintf (tmp, "%lx", (unsigned long int) offset);				\
        strcat (buf, tmp);					\
      }								\
      else if ((flags) & P_LDST) {				\
	if ((flags) & (F_USE_RT|F_USE_RTW)) {			\
	  sprintreg (buf, type, mi.imm.rt);			\
	  strcat (buf,",");					\
	}							\
	sprintf (tmp, "%d(", sext_16(mi.imm.imm));		\
        strcat (buf, tmp);					\
	sprintreg (buf, type, mi.imm.rs);			\
	strcat (buf,")");					\
      }								\
      else if ((flags) & P_BRANCH) {				\
	if (USE_RS (flags)) {					\
	  sprintreg (buf, type, mi.imm.rs);			\
	  strcat (buf, ",");					\
	}							\
	if (USE_RT (flags)) {					\
	  sprintreg (buf, type, mi.imm.rt);			\
	  strcat (buf, ",");					\
	}							\
	sprintf (tmp, "%d", 4*sext_16(mi.imm.imm));		\
        strcat (buf, tmp);					\
      }								\
      else if ((flags) & IMM_REG) {				\
	sprintreg (buf, type, mi.imm.rt);			\
	strcat (buf, ",");					\
	sprintreg (buf, type, mi.imm.rs);			\
        if ((flags) & F_SIGNED_IMM)				\
	  sprintf (tmp, ",%d", sext_16(mi.imm.imm));		\
	else							\
	  sprintf (tmp, ",0x%x", mi.imm.imm);			\
        strcat (buf, tmp);					\
      }								\
      break;

#include "opcodes.def"

  default:
    sprintf (buf,"[%08x] unknown mainop", mi.data);
    break;
  }
  return buf;
}

