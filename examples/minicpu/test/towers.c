#include <stdio.h>

char *A = "A";
char *B = "B";
char *C = "C";

char s[5];

#define TOWER_SIZE 6

void 
printmessage(int n, char *from_peg, char *to_peg)
{
  printf("Move disk %d from peg %s to peg %s\n",
	 n, from_peg, to_peg);
}

void 
towers(int n, char *from_peg, char *to_peg, char *aux_peg)
{
  if (n == 1) {
    printmessage(n, from_peg, to_peg);
    return;
  };

  towers(n-1, from_peg, aux_peg, to_peg);

  printmessage(n, from_peg, to_peg);

  towers(n-1, aux_peg, to_peg, from_peg);
}

int
main(int argc, char **argv)
{
  towers(TOWER_SIZE, A, C, B);
  exit(0);
}
