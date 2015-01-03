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
 *  $Id: mydis.c,v 1.2 2006/04/06 20:07:18 kca5 Exp $
 *
 *************************************************************************/
#include "dis.h"
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include "vpi_user.h"
#include "misc.h"

void disasm(void)
{
  int i, numargs;
  numargs = vpi_nargs();

  if (numargs == 0) {
    warning("Error -- display instruction needs at least one argument\n");
  }

  for (i=0; i < numargs; i++) {
    vpi_printf ("%s\n", mips_dis_insn (DIS_TYPE_NAMES, vpi_getarg_int(i+1)));
  }
}
