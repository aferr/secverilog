#include <stdio.h>
#include <fcntl.h>

int main ()
{
  int BUF_SIZE = 16, i, fin;
  char buf[BUF_SIZE];

  fin = open("security/rijndael/input_small.asc", O_RDONLY); 
  buf[0] = 0x95;
  
  // enable the following line gives wrong result 950000000000aa00
  read (fin, buf+1, BUF_SIZE);
  
  // enable the following lines gives the correct result 954b7572740aaa00
  /*
  buf[1] = 0x4b;
  buf[2] = 0x75;
  buf[3] = 0x72;
  buf[4] = 0x74;
  buf[5] = 0x0a;*/
 
  buf[6] = 0xaa;
  printf("The result is %llx\n", *((long long *)buf)); 
  exit(0);
}
