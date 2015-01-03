#ifndef __OPCODES_H
#define __OPCODES_H

#include "machine.h"

#define OPCODE_IMM(op,rs,rt,imm)       (((op)<<26)|((rs)<<21)|((rt)<<16)|(imm))
#define OPCODE_TGT(op,tgt)             (((op)<<26)|tgt)
#define OPCODE_REG(op,rs,rt,rd,sa,fn)  (((op)<<26)|((rs)<<21)|((rt)<<16)|  \
				        ((sa)<<6)|(fn))

typedef union {
  unsigned int data;
#if BYTE_ORDER == BIG_ENDIAN
  struct {
    unsigned int op:6;
    unsigned int rs:5;
    unsigned int rt:5;
    unsigned int imm:16;
  } imm;
  struct {
    unsigned int op:6;
    unsigned int tgt:26;
  } tgt;
  struct {
    unsigned int op:6;
    unsigned int rs:5;
    unsigned int rt:5;
    unsigned int rd:5;
    unsigned int sa:5;
    unsigned int func:6;
  } reg;
  struct {
    unsigned int op:6;
    unsigned int fmt:5;
    unsigned int ft:5;
    unsigned int fs:5;
    unsigned int fd:5;
    unsigned int func:6;
  } freg;
#else
  struct {
    unsigned int imm:16;
    unsigned int rt:5;
    unsigned int rs:5;
    unsigned int op:6;
  } imm;
  struct {
    unsigned int tgt:26;
    unsigned int op:6;
  } tgt;
  struct {
    unsigned int func:6;
    unsigned int sa:5;
    unsigned int rd:5;
    unsigned int rt:5;
    unsigned int rs:5;
    unsigned int op:6;
  } reg;
  struct {
    unsigned int func:6;
    unsigned int fd:5;
    unsigned int fs:5;
    unsigned int ft:5;
    unsigned int fmt:5;
    unsigned int op:6;
  } freg;
#endif
} MipsInsn;

#endif

