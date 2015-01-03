#ifndef __DIS_H
#define __DIS_H

#define DIS_TYPE_NUMBER 0x1
#define DIS_TYPE_NAMES  0x2

char *mips_dis_insn (int type, unsigned int ins);

#endif
