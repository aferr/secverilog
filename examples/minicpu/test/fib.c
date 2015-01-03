#include <stdio.h>

int rfib (int x)
{
  if (x == 0 || x == 1) return x;
  else return rfib(x-1) + rfib(x-2);
}

int ifib (int n)
{ 
  int x, y, z, i;

  if (n == 0 || n == 1) return n;
  x = 0; y = 1;
  for (i=2; i <= n; i++) {
	z = x + y;
	x = y;
	y = z;
  }
  return y;
}

int  main (void)
{ 
 int d;
 int i;
  d = 12;
 //d = 5;
 printf ("Series: ");
 for (i=1; i <= d; i++) {
	printf (" %d", rfib(i));
	if (ifib (i) != rfib (i)) {
		printf ("\n*** yow *** You're hosed\n");
	}
 }
 printf ("\n");
 exit (0);
}
