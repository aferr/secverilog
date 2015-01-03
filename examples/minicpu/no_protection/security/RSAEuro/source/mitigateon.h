/* use a special register for timing labels */
/*#define ENTER \
__asm__ __volatile__ ("li $tc,1");

#define EXIT \
__asm__ __volatile__ ("li $tc,0");
*/
#include "mitigateutil.h"

#ifndef EPOCH     
#define EPOCH
#define MITIGATE
int epoch=0;
#endif            

/* use annotated instruction for timing labels */
#define DECL(ID)  \
int start_ ## ID; \
int end_ ## ID;   \
int init_ ## ID;

#define RESET()   \
epoch=0;

/* turn on the mitigation */
#ifdef MITIGATE
#define ENTER(ID,PRED)   \
init_ ## ID = PRED;      \
READ_CLOCK(start_ ## ID) \
__asm__ __volatile__ ("nop/a");
#define EXIT(ID) \
__asm__ __volatile__ ("nop/b"); \
READ_CLOCK(end_ ## ID) \
end_ ## ID -= start_ ## ID; \
while (end_ ## ID > (1<<epoch)*init_ ## ID) \
  epoch++;                                  \
end_ ## ID = (1<<epoch)*init_ ## ID - end_ ## ID; \
SLEEP(end_ ## ID)
#else
/* turn off mitigation */
#define ENTER(ID,PRED)   \
__asm__ __volatile__ ("nop/a");
#define EXIT(ID) \
__asm__ __volatile__ ("nop/b");
#endif
