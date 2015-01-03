/* NIST Secure Hash Algorithm */

#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <time.h>
#include <fcntl.h>
#include "sha.h"
#include "label.h"

int main(int argc, char **argv)
{
    int fin;
    SHA_INFO sha_info;

//    if (argc < 2) {
//	fin = stdin;
//	sha_stream(&sha_info, fin);
//	sha_print(&sha_info);
//    } else {
//	while (--argc) {
//	    fin = fopen(*(++argv), "rb");
            fin = open("security/sha/input_small.asc", O_RDONLY);
	    if (fin < 0) {
		printf("error opening %s for reading\n", *argv);
	    } else {
		SETH
		sha_stream(&sha_info, fin);
		SETL
		sha_print(&sha_info);
		//fclose(fin);
		close(fin);
		exit(0);
	    }
//	}
//    }
    exit(0);
}
