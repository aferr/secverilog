#include <stdio.h>
#include <fcntl.h>

int main (int argc, char **argv)
{
    int BLOCK_SIZE = 1024, i, j, fin, fout;
    //unsigned char data[BLOCK_SIZE];
    // this is wrong somehow ..., the starting characters are missing
    unsigned char data[BLOCK_SIZE];

    printf("This print breaks code!");
    fin = open("../test/file.c", O_RDONLY);
    if (fin<0) {
        printf("error opening file.c for read\n");
        exit(1);
    }

    fout = open("../test/file_out.txt", O_WRONLY);
    if (fout<0) {
        printf("error opening file.c for read\n");
        exit(1);
    }

    while ((i =  read(fin, data, BLOCK_SIZE)) > 0) {
        for (j=0; j<i; j++) {
            printf ("%c", data[j]);
        }
        write(fout, data, i);
    }
    
    close(fin);
    close(fout);
    exit(0);
}
