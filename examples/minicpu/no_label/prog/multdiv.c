/*
 * $Id*
 *
 * The test program for mult/div
 *
 */

int main (void)
{
	int a, b;
	unsigned long long c, d;
        long long k;

	// mult
        printf("Test MULT ...\n");
	a = 12; 
	b = -3;
        k = a*b;
        printf("%d * %d = %lld\n", a, b, k);
        
        a = -1;
        b = -1;
        k = a*b;
        printf("%d * %d = %lld\n", a, b, k);

        a = -34567;
        b =  65987;
        k = (long long) a*b;
        printf("%d * %d = 0x%llx\n", a, b, k);

        a = 10000;
        b = 40000;
        k = a*b;
        printf("%d * %d = %lld\n", a, b, k);

        a = 0x800000cd;
        b = 0x7ffffeff;
        k = (long long) a*b;
        printf("%d * %d = 0x%llx\n", a, b, k);

        // multu
        printf("Test MULTU ...\n");
        c = 46;
        d = 6;
        printf("%lld * %lld = %lld\n", c, d, c*d);

        c = 10000;
        d = 40000;
        printf("%lld * %lld = %lld\n", c, d, c*d);
        
        c = 0x800000cd;
        d = 0x7ffffeff;
        printf("%lld * %lld = 0x%llx\n", c, d, c*d);

        c = 0xffffffff;
	d = 0xffffffff;
        printf("%lld * %lld = 0x%llx\n", c, d, c*d);

	// multu
	c = 0xffffffff;
	d = 5;
        printf("%lld * %lld = %lld\n", c, d, c*d);

	// div
        printf("Test DIV ...\n");
	a = -7;
	b = 3;
        printf("%d / %d = %d\n", a, b, a/b);
        printf("%d %% %d = %d\n", a, b, a%b);

        a = -1;
        b = -1;
        printf("%d / %d = %d\n", a, b, a/b);
        printf("%d %% %d = %d\n", a, b, a%b);

        a =  13;
        b = -55;
        printf("%d / %d = %d\n", a, b, a/b);
        printf("%d %% %d = %d\n", a, b, a%b);

        a = 0x800000cd;
        b = 0x000ffeff;
        printf("%d / %d = %d\n", a, b, a/b);
        printf("%d %% %d = %d\n", a, b, a%b);

	// divu
        printf("Test DIVU ...\n");
	c = 0xffffffff;
	d = 12;
        printf("%lld / %lld = %lld\n", c, d, c/d);
        printf("%lld %% %lld = %lld\n", c, d, c%d);

        c = 46;
        d = 6;
        printf("%lld / %lld = %lld\n", c, d, c/d);
        printf("%lld %% %lld = %lld\n", c, d, c%d);
        
        c = 10000;
        d = 40000;
        printf("%lld / %lld = %lld\n", c, d, c/d); 
        printf("%lld %% %lld = %lld\n", c, d, c%d);
        
        c = 0x800000cd;
        d = 0x7ffffeff;
        printf("%lld / %lld = %lld\n", c, d, c/d);
        printf("%lld %% %lld = %lld\n", c, d, c%d);
        
        c = 0xffffffff;
        d = 0xffffffff;
        printf("%lld / %lld = %lld\n", c, d, c/d);
        printf("%lld %% %lld = %lld\n", c, d, c%d);
        
        exit(0);
}
