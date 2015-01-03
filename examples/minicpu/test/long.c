#define RAND(a,b) (((a = 36969 * (a & 65535) + (a >> 16)) << 16) + (b = 18000 * (b & 65535) + (b >> 16)))

int main (void)
{
    static unsigned long long a[2];
    a[0] = 0xeaf3;
    a[1] = 0x35fe;

    unsigned long long r = RAND(a[0], a[1]);
    // local machine reports: 84891c7f5360
    // our mips machine reports: 1c7f5360
    printf("The result is %llx\n", r);
    exit(0);
}
