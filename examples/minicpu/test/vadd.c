#include <stdio.h>

#define ROW_SIZE	32
#define COL_SIZE	32
#define UNROLL_FACTOR	4

int A[ROW_SIZE][COL_SIZE];
void DoIt(void);

int 
main(int argc, char **argv)
{
   DoIt();
   printf("The answer to all life's questions is %d \n",
	  A[ROW_SIZE-1][COL_SIZE-1]);
   exit(99);
}

void
DoIt(void)
{
   int i,j;

   for (i=0; i < ROW_SIZE; i++) {
      for (j=0; j < COL_SIZE; j+= UNROLL_FACTOR) {
	 A[i][j] = i + j + (i << 4) ^ (j >> 1);
	 A[i][j+1] = i + j + (i << 3) ^ (j >> 1);
	 A[i][j+2] = i + j + (i << 2) ^ (j >> 1);
	 A[i][j+3] = i + j + (i << 1) ^ (j >> 1);
      }
   }
}

