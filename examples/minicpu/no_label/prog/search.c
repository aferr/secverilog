#include "label.h"

#define SIZE 1000

int search(int* x, int key)
{
	int i;
	for( i=0;i<SIZE;i++ )
	{
		if(x[i] == key) return i;
	}
	return -1;
}

int main ()
{
  int i, k;
  int a[SIZE];
  int key[10] = {250000, 422321, 42315, 12, 0, 999, 1996, 7894, 533, 100};
  
  for (i = 0;i<SIZE;i++) {
  	a[i] = i*(SIZE-i);
  }
  
  SETH
  for( i=0;i<10;i++) 
  	search(a, key[i]);
  SETL
	  
  exit(0);
  
}