#include <stdio.h>

#define TYPE int
#define SIZE 87

TYPE x[SIZE];
TYPE y[SIZE];

void init (void)
{
   int i;

   x[0] = 3;
   x[1] = 7;
   for (i=1; i < SIZE-1; i++) {
      x[i+1] = x[i]+(x[i-1]^128);
   }
}

void dumpoutput (void)
{
   int i;
   int flag = 0;
   
   for (i=1; i < SIZE; i++) {
      if (x[i] < x[i-1]) {
	 flag = 1;
	 printf ("Error at position %d\n", i);
      }
   }
   if (!flag) printf ("Array sorted correctly.\n");
}
      
   
void mergesort (unsigned long n, TYPE *array, TYPE *array2)
{
  TYPE *p, *q, *r;
  unsigned long int i, j, k, l, m, t, k1;
  unsigned long log2;

  if (n==0) return;

  p = array; q = array2;
  for(log2=0,i=1; i < n; i*=2, log2++) ;
  for (i=1, k=2; i <= log2; i++, k*=2) {
        for (j=0; j < n; j += k) {
                l = j; m = j+(k>>1);
                if ((n-j) < k) k1 = n-j; else k1 = k;
                for (t=0; t < k1; t++)
                        if (l < (j+(k>>1)))
                                if (m < j+k1)
                                        if (p[l] < p[m]) q[j+t] = p[l++];
                                        else q[j+t] = p[m++];
                                else
                                        q[j+t] = p[l++];
                        else
                                q[j+t] = p[m++];
        }
        r = p; p = q; q = r;
  }
  if (array != p) for (i=0; i < n; i++) *array++ = *p++;
}


int main (void)
{		
   init ();
   mergesort (SIZE, x, y);
   dumpoutput ();
   exit(0);
}
