/*************************************************************************
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
 *  $Id: misc.c,v 1.2 2006/04/06 19:27:56 kca5 Exp $
 *
 *************************************************************************/
#include <stdio.h>
#include <stdarg.h>
#include <string.h>
#include "misc.h"
#include "vpi_user.h"


/*-------------------------------------------------------------------------
 * print error message and die.
 *-----------------------------------------------------------------------*/
void fatal_error (char *s, ...)
{
  va_list ap;

  fprintf (stderr, "FATAL: ");
  va_start (ap, s);
  vfprintf (stderr, s, ap);
  va_end (ap);
  fprintf (stderr, "\n");
  exit (1);
}

/*-------------------------------------------------------------------------
 * warning
 *-----------------------------------------------------------------------*/
void warning (char *s, ...)
{
  va_list ap;

  fprintf (stderr, "WARNING: ");
  va_start (ap, s);
  vfprintf (stderr, s, ap);
  va_end (ap);
  fprintf (stderr, "\n");
}


char *Strdup (char *s)
{
  char *t;

  MALLOC (t, char, strlen(s)+1);
  strcpy (t, s);

  return t;
}


/*--
 * VPI utility functions
 *--*/

/**
 * Gets an iterator for the task or function's arguments.
 * @return A valid iterator, or NULL if there are no arguments.
 * Notes: Use vpi_scan to scan through the given iterator.
 */
vpiHandle get_arg_itr()
{
  vpiHandle tfH;
  /* Get task handle */
  tfH = vpi_handle(vpiSysTfCall,NULL);
  if (!tfH)
    {
      fatal_error("Failed to get a task handle\n");
    }
  /* Get handle to an iterator for the arguments */
  return (vpi_iterate(vpiArgument,tfH)); /*NULL if no args*/
}

/**
 * Sets the function return value to the given value.
 * @param num Ignored (FIXME)
 * @param value long long integer value to return
 */
void vpi_set_retval(int num,long long value)
{
  s_vpi_value new_value;
  
  vpiHandle tfH = vpi_handle(vpiSysTfCall,NULL);
  if (!tfH)
    {
      fatal_error("Failed to get a task handle\n");
    }
  new_value.format = vpiIntVal;
  new_value.value.integer = value; 
  vpi_put_value(tfH, &new_value, NULL, vpiNoDelay);
}

/**
 * Return the number of arguments for this system task/func.
 */
int vpi_nargs(void)
{
  vpiHandle argI,argH;
  int i = 0;
  argI = get_arg_itr();
  if (argI == NULL)
    return 0;

  while ((argH = vpi_scan(argI)))
    i++;
  return i;
}

/**
 * Get the argument at the given position.
 * @param arg_num Argument number, starting from 1.
 * @return the VPI value structure corresponding to the argument.
 */
s_vpi_value vpi_getarg_generic(int arg_num, PLI_INT32 format)
{
  vpiHandle argI, argH;
  s_vpi_value got_value;
  int i = 1;
  argI = get_arg_itr(); // Get the arguments
  if (argI == NULL)
    fatal_error("This task/function expected to get some arguments.");

  // Iterate through the arguments until we find the correct arg.
  while((argH = vpi_scan(argI)))
    {	
      if (i == arg_num){
	// Retrieve the value in the requested format.
	got_value.format = format;
	vpi_get_value(argH, &got_value);

	// Free the iterator object, because we return before reaching end.
	vpi_free_object(argI);

	// Return the retrieved value.
	return got_value;
      }
      i++;
    }

  fatal_error("Trying to get argument %d for task/function given only %d arguments.", arg_num, vpi_nargs());
  return got_value; // never actually reached.
}

/**
 * Get the integer argument at the given position.
 * @param arg_num Argument number, starting from 1.
 * @return the integer value of the argument
 */
long long vpi_getarg_int(int arg_num)
{
  s_vpi_value got_value = vpi_getarg_generic(arg_num, vpiIntVal);
  return got_value.value.integer;
}

/**
 * Get the string argument at the given position.
 * @param arg_num Argument number, starting from 1.
 * @return the integer value of the argument
 */
char* vpi_getarg_string(int arg_num)
{
  s_vpi_value got_value = vpi_getarg_generic(arg_num, vpiStringVal);
  return got_value.value.str;
}

