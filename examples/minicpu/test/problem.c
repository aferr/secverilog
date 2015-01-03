/*
 * $Id*
 *
 * The test program 
 *
 */
#include <stdio.h>

int  main (void)
{
	int a, b, i, j, k;
	unsigned c;
	signed char array[10];

	// Problem 1
	// The following code excutes simple arithmetic/logical operations.
	a = 1;  
	b = -1; 
	if(a+(a&b)+(a|b)+(a^b)-b) 
		// MIPS machine has a problem.
		printf("Problem 1 : There is something WRONG!!\n"); 
	else
		// Problem 1 is solved.
		printf("Problem 1 is solved!!\n");

	// Problem 2
	// The following code excutes simple arithmetic/logical operations.
	a = 0xffffffff;  
	c = 0xffffffff; 
	if(((a >> 8) == (c >> 8)) || ((a << 16) != (c << 16))) 
		// MIPS machine has a problem.
		printf("Problem 2 : There is something WRONG!!\n"); 
	else
		// Problem 2 is solved.
		printf("Problem 2 is solved!!\n");

	// Problem 3
	// The following code calculates k = 1+2+3+4+5+6+7+8+9+10 = 55
	k = 0;
	for(i = 10; i > 0; i--){
		j = i;
		while(j > 0){
			k++;
			j--;
		}
	}
	if(k !=  55)
		// MIPS machine has a problem.
                printf("Problem 3 : There is something WRONG!!\n");
	else
		// Problem 3 is sloved.
		printf("Problem 3 is solved!!\n");

	// Problem 4
	// The following code calculates k = 55-10-9-8-7-6-5-4-3-2-1 = 0 
	for(i = 1; i <= 10; i++)
		array[i-1] = -i;
	k = 55;
	for(i = 0; i < 10; i++)
		k += array[i];
	if(k != 0)
		// MIPS machine has a problem.
                printf("Problem 4 : There is something WRONG!!\n");
	else
		// Problem 4 is sloved.
		printf("Problem 4 is solved!!\n");


	exit (1);
}
