#include <stdio.h>

typedef unsigned long long LL;
typedef unsigned char Byte;

int factorial (int n)
{
  if (n <= 0) return 1;
  else return n + factorial (n-1);
}

char *endianness (void)
{
  long *l;
  char c[4];
  
  l = (long*)c;

  c[0] = 1;
  c[1] = 0;
  c[2] = 0; 
  c[3] = 0;

  if (*l == 1)
    return "little";
  else
    return "big";
}

int main (void)
{
  int i, j;
  LL data[4];
  Byte buf[128];

  printf ("Does a mips-sgi-irix5 binary work on an x86?\n");
  printf ("In spite of what libbfd docs say?\n");
  printf ("Your host seems to be of type %s-endian\n", endianness ());
  printf ("Summation\n\n");
  i = 5;
  do {
    printf ("Int: ");
    //scanf ("%i", &i);
    j = factorial (i);
    printf ("sum %d = %d\n", i, j);
    i--;
  } while (i > 0);
  
  exit(0);
}
