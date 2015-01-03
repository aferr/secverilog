/* utility functions */
#define READ_CLOCK(var) \
var = 0;

/* the hardware use register $inc to update clock */
#define SLEEP(var) \
var = 10; \
__asm__ __volatile__ ("nop"); \
__asm__ __volatile__ ("nop"); \
__asm__ __volatile__ ("nop"); \
__asm__ __volatile__ ("nop");
/* nops are used to make sure the clock is updated */
