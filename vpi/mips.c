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
 *  mips.c, 2005 July 28, wxl2
 *
 *************************************************************************/
#include <stdio.h>
#include <string.h>
#include "mem.h"
#include "vpi_user.h"
#include "pli.h"
#include "misc.h"

Mem *physical_memory = NULL;

#define MAX_TEST_FILES  256
#define MAX_NAME_LENGTH 256

int uloader (char *);
char testlist[MAX_TEST_FILES*MAX_NAME_LENGTH];
int nextTest;
int numTests;

/*--------------------------------------

Function:	seed_mm
Description:	Seed main memory from a data file

--------------------------------------*/

void seed_mm(void)
{
   char buf[1024];
   char *filename;
   int temp;
   if (vpi_nargs() == 0) {
     vpi_printf ("Enter file name: "); fflush (stdout);
     if (!fgets (buf, 1024, stdin)) {
       fprintf (stderr, "-- unexpected end-of-file\n");
       exit (1);
     }
     if (strlen (buf) == 0) {
       fprintf (stderr, "-- wish you had entered a file name\n");
       exit (1);
     }
     buf[strlen(buf)-1] = '\0';
     filename = buf;
   }
   else if (vpi_nargs() == 1) {
     filename = vpi_getarg_string(1);
   }
   else {
     vpi_printf("Error -- Incorrect number of parameters\n");
     exit (1);
   }


   temp = uloader(filename);
   //printf ("uloader = %d\n",temp);

   // Actually load this file. This is a super-simplified uloader for
   // ECE 314. Our image files include the boot section, so we just
   // load one single file.
   /*   if (physical_memory) {
     Clear (physical_memory);
   }
   else {
     physical_memory = new_Mem();
   }

   // load the specified file.
   temp = ReadImageS (physical_memory,filename);
   printf("ReadImageS = %d\n",temp);
   if (!temp) {
     fprintf (stderr, "Memory image file %s not found.\n", filename);
     exit (1);
     }*/
}

void readLine(char* buffer, FILE* source, int n) {
  // Copy at most n-1 characters from source to buffer.
  // Stops at newline and null characters.
  // Appends a null character to end of buffer.
  int i;
  for(i = 0; i < n-1; i++) {
    char c = (char) fgetc(source);
    if((c == 0) || (c == '\n')) {
      buffer[i] = 0;
      break;
    } else {
      buffer[i] = c;
    }
  }
}

//custom test function
void seed_mm_test(void){
  char* testdir = "test/testlist.txt";
  
  FILE* in = fopen(testdir, "r");
  
  if(in == NULL){
    fprintf(stderr, "test/testlist.txt not found.\n");
    exit(1);
  }
  
  char buffer[MAX_NAME_LENGTH];
  vpi_printf ("-----------------------------------------------------------------------\n");
  vpi_printf ("Reading test/testlist.txt:\n");
  for(numTests = 0; fgets(buffer, MAX_NAME_LENGTH, in) != NULL; numTests++){
    if(numTests >= MAX_TEST_FILES) {
      fprintf(stderr, "No more than %d test files permitted.\n", MAX_TEST_FILES);
      break;
    }
    if(strlen(buffer) == 0) break;
    
    strncpy(testlist + (MAX_NAME_LENGTH*numTests), buffer, MAX_NAME_LENGTH);
    testlist[(MAX_NAME_LENGTH*numTests) + strlen(buffer) - 1] = 0; // removes newline char
    fprintf(stdout, " -> %s\n", testlist + (MAX_NAME_LENGTH*numTests));
  }
  vpi_printf ("-----------------------------------------------------------------------\n");
  
  fclose(in);
  nextTest = 0;
}

//load the next test on the testlist array
//returns 0 if no more tests left to be performed
//returns 1 if still tests left
unsigned int load_next_test(void){
   FILE *fp;
   char buf[1024];
   unsigned int entry_point;
   
   char* filename = testlist + (MAX_NAME_LENGTH*nextTest);
   if(strlen(filename) == 0) {
     vpi_set_retval(0, (long long)0);
     return 0; // dummy value ss868
   }
   
   if (physical_memory) {
     Clear (physical_memory);
   }
   else {
     physical_memory = new_Mem();
   }
   
   // Load image file
   if (!ReadImageS (physical_memory, filename)) {
     fprintf(stderr, "File `%s': Image file not found\n", filename);
     exit (1);
   }
   
   if (strlen(filename) > 1000) {
     fprintf (stderr, "You are killing me\n");
     exit (1);
   }
   sprintf (buf, "%s.inf", filename);
   
   fp = fopen (buf, "r");
   if (!fp) {
     fprintf (stderr, "Error: `%s' info file missing!\n", filename);
     exit (1);
   }
   fscanf(fp, "%li", (long int *) &entry_point);
   fclose (fp);
   
   // Display information to user
   vpi_printf ("Running `%s': ", filename);
   
   if(nextTest < numTests) {
     vpi_set_retval(0, (long long)1);
     nextTest++;
   }
   else{
     vpi_set_retval(0, (long long)0);
   }
   return 0; // dummy value ss868
}


/*---------------------------------------

Function:	load_mm
Description:	Load data from main memory

---------------------------------------*/


unsigned int load_mm(void) // 32 bits
{
  //printf("load_mm");
  unsigned int address = 0; // 32 bits
  if (!physical_memory) {
    vpi_printf ("$load_mm Error -- no memory image loaded!\n");
    //return ;//vpi_set_retval(0,0xdeadbeef);
    return 0; // dummy value ss868
  }
  if (vpi_nargs() != 1) {
    vpi_printf("$load_mm Error -- Incorrect number of parameters\n");    
    //return;//vpi_set_retval(0,0xdeadbeef);
    return 0; // dummy value ss868
  }
  address = vpi_getarg_int(1);
  //address = address & 0x00000000ffffffff;
  // printf(" --- address=%x",address);
  //printf(" -----what's in the memory: %x\n", BEReadWord (physical_memory, address));
  vpi_set_retval(0,BEReadWord (physical_memory, address));
  return 0; // dummy value ss868
}


/*--------------------------------------

Function:	store_mm
Description:	Store data to main memory

---------------------------------------*/
void store_mm(void)
{
  //printf("***store_mm  --");
  unsigned int address;
  unsigned int data;
  unsigned long long temp;
   if (!physical_memory) {
     vpi_printf ("Error -- no memory image loaded!\n");
     return;
   }

   if (vpi_nargs() != 2)
     vpi_printf("Error -- Incorrect number of parameters.\n");
   else
   {
     address = vpi_getarg_int(1);
     //address = address & 0x00000000ffffffff;
     data = vpi_getarg_int(2);
     temp = Read(physical_memory,address);
     //printf("address == %x   data == %x\n",address, data);
     BEWriteWord (physical_memory, address, data);
   }
}

/*--------------------------------------
Kunle's routines...
---------------------------------------*/

/********************************************************************
*	Copyright (C) 1989, The University of Michigan		    *
********************************************************************/

/* mmu.c --	Manages physical memory for the GMP simulation
 *
 * Kunle Olukotun
 *
 * HISTORY
 *       Aug  89 Olukotun: Original code.
 *       Sept 90 Olukotun: Revised to work with Verilog.
 *
 */

int uloader(char *filename)
{
   FILE *fp;
   char buf[1024];
   unsigned int entry_point;

   if (physical_memory) {
     Clear (physical_memory);
   }
   else {
     physical_memory = new_Mem();
   }

   // load boot code
   // Changed to ReadImageS
   if (!ReadImageS (physical_memory,"boot.image")) {
     fprintf (stderr, "Boot file: Boot file not found\n");
     exit (1);
   }

   // load image file
   // Changed to MergeImageS
   if (!MergeImageS (physical_memory, filename)) {
     fprintf (stderr, "File `%s': Image file not found\n", filename);
     exit (1);
   }

   if (strlen (filename) > 1000) {
     fprintf (stderr, "You are killing me\n");
     exit (1);
   }
   sprintf (buf, "%s.inf", filename);
   
   fp = fopen (buf, "r");
   if (!fp) {
     fprintf (stderr, "Error: `%s' info file missing!\n", filename);
     exit (1);
   }
   fscanf(fp, "%li", (long int *) &entry_point);
   // No need to load gp value under mipseb-linux
   //fscanf (fp, "%i %i", &entry_point, &gp_value);
   fclose (fp);

   // Set entry point register
   // lui $at, $0, entry_point[31:16] 3c01
   // ori $at, $0, entry_point[15:0] 3821

   // The instructions to be written
   unsigned long long lui_at, ori_at;   
   lui_at = 0x3c010000 | (entry_point >> 16);
   ori_at = 0x34210000 | (entry_point & 0xffff);
   // The double word aligned instructions
   unsigned long long set_at = ((lui_at << 32) | ori_at);
      Write(physical_memory, 0xbfc00008, set_at);
 
   // Original code neglected the lui for $gp and $at
   // li $gp, gp_value
   //BEWriteWord (physical_memory, 0xbfc00000,
   //			 0x3c1c0000 | ((gp_value >> 16) & 0xffff));

   //BEWriteWord (physical_memory, 0xbfc00004,
   //			 0x379c0000 | (gp_value & 0xffff));
   // li $r1, entry_point
   //BEWriteWord (physical_memory, 0xbfc00008,
   //				 0x3c010000 | ((entry_point>>16) & 0xffff));

   //BEWriteWord (physical_memory, 0xbfc0000c,
   //			 0x34210000 | (entry_point & 0xffff));

   // Display information to user
   vpi_printf ("Loaded Executable `%s'\n", filename);
   vpi_printf 
     ("-----------------------------------------------------------------------\n");   
   vpi_printf ("Boot code entry point: 0x%08x\n", 0xbfc00000);
   vpi_printf ("User code entry point: 0x%08x\n", entry_point);
   //vpi_printf ("Global pointer: 0x%08x\n", gp_value);
   vpi_printf ("Stack pointer: 0x%08x\n", 0x7fffefff);
   vpi_printf
     ("-----------------------------------------------------------------------\n");
   vpi_printf("\n");

   // dumps the merged boot image and user image so we can inspect it
   //fp = fopen("dumpedimage","w");
   //DumpImage(physical_memory, fp);
   //fclose(fp);
   return 0; // dummy value ss868
} 
