#ifndef __MISC_H
#define __MISC_H

#include <stdlib.h> /* malloc.h is deprecated */
#include <stdio.h>
#include "vpi_user.h"

#define MALLOC(var,type,size) do { if (size == 0) { fprintf (stderr, "FATAL: allocating zero-length block.\n\tFile %s, line %d\n", __FILE__, __LINE__); exit (2); } else { var = (type *) malloc (sizeof(type)*(size)); if (!var) { fprintf (stderr, "FATAL: malloc of size %d failed!\n\tFile %s, line %d\n", (int)(sizeof(type)*(size)), __FILE__, __LINE__); fflush(stderr); exit (1); } } } while (0)

#define REALLOC(var,type,size) do { if (size == 0) { fprintf (stderr, "FATAL: allocating zero-length block.\n\tFile %s, line %d\n", __FILE__, __LINE__); exit (2); } else { var = (type *) realloc (var, sizeof(type)*(size)); if (!var) { fprintf (stderr, "FATAL: realloc of size %d failed!\n\tFile %s, line %d\n", (int)(sizeof(type)*(size)), __FILE__, __LINE__); exit (1); } } } while (0)

#define NEW(var,type) MALLOC(var,type,1)
#define FREE(var)   free(var)

#define Max(a,b) ( ((a) > (b)) ? (a) : (b) )

void fatal_error (char *s, ...);
void warning (char *s, ...);
char *Strdup (char *);

#define Assert(a,b) do { if (!(a)) { fprintf (stderr, "Assertion failed, file %s, line %d\n", __FILE__, __LINE__); fprintf (stderr, "Assertion: " #a "\n"); fprintf (stderr, "ERR: " b "\n"); exit (4); } } while (0)

#define MEMCHK(x)  Assert (x, "out of memory")



/*---
 * VPI utility functions
 *---*/

vpiHandle get_arg_itr();

/**
 * Sets the function return value to the given value.
 * @param num Ignored (FIXME)
 * @param value long long integer value to return
 */
void vpi_set_retval(int num,long long value);

/**
 * Return the number of arguments for this system task/func.
 */
int vpi_nargs(void);

/**
 * Get the argument at the given position.
 * @param arg_num Argument number, starting from 1.
 * @return the VPI value structure corresponding to the argument.
 */
s_vpi_value vpi_getarg_generic(int arg_num, PLI_INT32 format);

/**
 * Get the integer argument at the given position.
 * @param arg_num Argument number, starting from 1.
 * @return the integer value of the argument
 */
long long vpi_getarg_int(int arg_num);

/**
 * Get the string argument at the given position.
 * @param arg_num Argument number, starting from 1.
 * @return the integer value of the argument
 */
char* vpi_getarg_string(int arg_num);


#endif
