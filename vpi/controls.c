#include <stdio.h>
#include <string.h>
#include <assert.h>
#include <errno.h>

#include "controls.h"
#include "vpi_user.h"
#include "vpi_user_cds.h"
#include "veriuser.h" /* for tf_dofinish */
#include "dis.h"
#include "misc.h"
#include "opcode_consts.h"

//#define WARN_ON_USE

#define CACHE_FILE_NAME "control_cache"
#define NOT_IN_CACHE (-1)

/**
 * Print a fatal error and return.
 */
void vpi_fatal_error(char* fmt, ...) {
  va_list ap;
  vpiHandle hTask;

  va_start(ap, fmt);

  hTask = vpi_handle(vpiSysTfCall, NULL);
  vpi_printf("\n  Error in system task %s:\n",
	     vpi_get_str(vpiName, hTask));
  vpi_printf("  In %s, line %d\n",
	     vpi_get_str(vpiFile, hTask),
	     vpi_get(vpiLineNo, hTask));
  vpi_vprintf(fmt, ap);
  va_end(ap);
  vpi_printf("\n");

  tf_dofinish();
}
  
int vpi_get_int(vpiHandle hArg) {
  s_vpi_value val;

  val.format = vpiIntVal;
  vpi_get_value(hArg, &val);
  return val.value.integer;
}

/**
 * Compare two instructions for the same operation.
 * @return 1 if the operations are equal.
 */
int ins_eq(unsigned int ins1, unsigned int ins2)
{
  /* Extract the instruction fields. */
  unsigned int op1, op2, func1, func2, rt1, rt2;
  op1 = (ins1 >> 26)&0x3f;
  func1 = (ins1 & 0x3f);
  rt1 = (ins1 >> 16) & 0x1f;

  op2 = (ins2 >> 26)&0x3f;
  func2 = (ins2 & 0x3f);
  rt2 = (ins2 >> 16) & 0x1f;

  if (op1 != op2) return 0;
  
  if (op1 == OP_SPECIAL)
    return func1 == func2;

  if (op1 == OP_REGIMM)
    return rt1 == rt2;

  /* If we get here, then opcodes are equal and are not SPECIAL or REGIMM. */
  /* Therefore the operations must be the same. */
  return 1;
}

/**
 * Gets a value from the cache.
 * @param ins the MIPS instruction to look for
 * @param name the name of the control signal
 * @return the value of the control signal, or -1 (NOT_IN_CACHE)
 *  if it is not in the cache.
 */
int get_cache(unsigned int ins, char* name)
{
  FILE* fp;
  unsigned int tmpins;
  char tmpname[33];
  int val;
  int lineno = 0;

  fp = fopen(CACHE_FILE_NAME, "r");
  if (!fp) {
    if (errno == ENOENT)
      return NOT_IN_CACHE; /* because the cache file does not exist. */

    /* Otherwise, there is some real error. */
    vpi_fatal_error("Error opening cache file: %s", strerror(errno));
  }
  
  /* Loop through all lines in the file. */
  while (!feof(fp)) {
    int ret = fscanf(fp, "%8lx %32s %x", (long unsigned int *) &tmpins, tmpname, &val);
    if (ret == EOF) break;
    lineno++;
    if (ret != 3) {
      fprintf(stderr, "Warning: Skipping invalid line %d in cache file.\n", lineno);
      continue;
    }
    
    /* See if this line matches. */
    if (strcmp(name, tmpname) == 0 && ins_eq(ins, tmpins)) {
      /* Got a match. Return the value. But close the file first! */
      fclose(fp);
      return val;
    }
  }

  /* No go. Close the file and return error. */
  fclose(fp);
  return NOT_IN_CACHE;
}

/**
 * Stores the instruction control signal value in the cache.
 * Note: The value must not previously be in the cache, or
 *  this will silently do the wrong thing.
 * @param ins the MIPS instruction to store
 * @param name the name of the control signal
 * @param val the value of the control signal
 */
void store_cache(unsigned int ins, char* name, int val)
{
  FILE* fp;

  /* Make sure the value is not in the cache. This is an expensive
     check, so FIXME it should be ifdefed. */
  assert(get_cache(ins, name) == NOT_IN_CACHE);

  /* Open the cache file for appending. */
  if ((fp = fopen(CACHE_FILE_NAME, "a")) == NULL)
    vpi_fatal_error("Error opening cache file: %s", strerror(errno));
  
  /* Append the new line. */
  fprintf(fp, "%08lx %s %x\n", (long unsigned int) ins, name, val);

  fclose(fp);
}

int get_value_for_ins(unsigned int ins, char* destName, int destSize)
{
#ifdef READ_BINARY
  /* big enough to hold 32 bits, the terminating NULL, and room to spare. */
  char buf[64];
  int len; /* actual length of the entered data */
  /* other temporaries */
  int i;
#endif

  /* one more than the maximum value of the destination, given the
   * requested size */
  int destMax = 1 << destSize;

  /* the final value */
  int val;
  
  if (destSize < 1 || destSize > 32)
    vpi_fatal_error("Invalid size requested for %s: %d", destName, destSize);

  /* Check the cache. */
  val = get_cache(ins, destName);
  if (val != NOT_IN_CACHE) {
    /* Check the cache consistency with the size. */
    if (val >= destMax)
      vpi_fatal_error("Cache consistency check failed: the cached value %x is too big to\n"
		      "fit in %d bits. Perhaps you changed the size of control signal %s.\n"
		      "Manually edit " CACHE_FILE_NAME " and remove the erroneous line.\n",
		      val, destSize, destName);
    
    /* Otherwise, we got the value successfully from cache. */
    return val;
  }

  fprintf(stderr, " For instruction %s:\n", mips_dis_insn(DIS_TYPE_NAMES, ins));
  if (destSize == 1)
    fprintf(stderr, "  %s: ", destName);
  else
    fprintf(stderr, "  %s: %d'h", destName, destSize);
  
  /* Read the value. */
#ifdef READ_BINARY
  if (fgets(buf, sizeof buf, stdin) == NULL)
    vpi_fatal_error("Error while reading in value.");
  len = strlen(buf);
  if (buf[len - 1] == '\n') { /* ... which it should... */
    buf[len - 1] = '\0';
    len--;
  }

  /* Check the length. */
  if (len != destSize)
    vpi_fatal_error("Wrong number of bits specified. (Note: The value must be in binary.)");
  
  /* Parse the binary value. */
  val = 0;
  for (i=0; i<destSize; i++) {
    if (buf[i] != '0' && buf[i] != '1')
      vpi_fatal_error("Binary input (0 or 1) required.");

    val <<= 1;
    val |= (buf[i] == '1');
  }
#else
  scanf("%x", &val); /* read hex. */
  if (val < 0)
    vpi_fatal_error("Negative entry is not supported. Enter the value as if it were unsigned.\nRemember that the value entered is in hex format.");
  if (val >= destMax)
    vpi_fatal_error("Value entered is too large to fit within %d bits (0 through 'h%x).\n", destSize, destMax-1);
#endif

  store_cache(ins, destName, val);

  return val;
}


/**
 * Prompts for the value of a control signal given an instruction.
 *
 * Example usage: $get_value(INS, Signed);
 *  Where:
 *   INS is the MIPS instruction to which the control signal corresponds
 *   Signed is a reg that will get the value.
 */
PLI_INT32 get_value(PLI_BYTE8 *unused)
{
  vpiHandle hTask, hArgIter, hArg;
  s_vpi_value val;
  unsigned int ins;
  char* destName;
  int destSize;
  vpiHandle hDest;
  int destVal;

  printf("get_value used\n");

#ifdef WARN_ON_USE
  static int already_warned = 0;
  if (!already_warned) {
    fprintf(stderr,
	    "\n\n"
	    "WARNING: $get_value was used. The final project submission cannot use any\n"
	    "behavioral Verilog, including this task. Please remove all uses (and all\n"
	    "'reg's) before submission.\n\n"
	    "Press Enter to continue.\n");
    getchar();
    already_warned = 1;
  }
#endif

  /* get the arguments to this task. */
  hTask = vpi_handle(vpiSysTfCall, NULL);
  hArgIter = vpi_iterate(vpiArgument, hTask);

  /* Make sure there are some arguments. */
  if (vpi_chk_error(NULL))
    vpi_fatal_error("No parameters given.");

  /* Get the first argument, the instruction, as an int. */
  hArg = vpi_scan(hArgIter);
  if (!hArg)
    vpi_fatal_error("Error getting instruction argument.");

  ins = vpi_get_int(hArg);

  /* Next is the dest reg. */
  hArg = vpi_scan(hArgIter);
  if (!hArg)
    vpi_fatal_error("Error getting destination argument.");

  if (vpi_get(vpiType, hArg) != vpiReg)
    vpi_fatal_error("Second argument must be a reg.");

  hDest = hArg;

  /* Make sure there are no more arguments */
  while((hArg = vpi_scan(hArgIter)))
    vpi_fatal_error("Too many arguments given.");

  destName = vpi_get_str(vpiName, hDest);
  destSize = vpi_get(vpiSize, hDest);

  destVal = get_value_for_ins(ins, destName, destSize);

  /* Set the final value. */
  val.format = vpiIntVal;
  val.value.integer = destVal;
  vpi_put_value(hDest, &val, NULL, vpiNoDelay);

  return 0;
}
