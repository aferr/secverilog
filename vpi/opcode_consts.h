/*-*-mode:c++-*-**********************************************************
 *
 *  Copyright (c) 1999 Cornell University
 *  Computer Systems Laboratory
 *  Cornell University, Ithaca, NY 14853
 *  All Rights Reserved
 *
 *  Permission to use, copy, modify, and distribute this software
 *  and its documentation for any purpose and without fee is hereby
 *  granted, provided that the above copyright notice appear in all
 *  copies. Cornell University makes no representations
 *  about the suitability of this software for any purpose. It is
 *  provided "as is" without express or implied warranty. Export of this
 *  software outside of the United States of America may require an
 *  export license.
 *
 *  $Id: opcode_consts.h,v 1.1 2006/05/21 02:35:53 kca5 Exp $
 *
 **************************************************************************
 */
#ifndef __OPCODES_H__
#define __OPCODES_H__ 

/* Jump Branch Info Conditions */
#define JBI_NO          0
#define JBI_NOTTAKEN    1
#define JBI_TAKEN       2

/* Result Codes for OneStep() */
#define RES_OK          0
#define RES_UNIMPL      1
#define RES_ALIGN       2
#define RES_OFLO        3
#define RES_ERROR       4

/*
 *   Opcodes for different types of instructions
 */

/* 
 *  Type 1: Instructions with different opcodes
 */
#define OP_j 		0x2
#define OP_jal 		0x3
#define OP_beq 		0x4
#define OP_bne 		0x5
#define OP_blez 	0x6
#define OP_bgtz 	0x7
#define OP_addi 	0x8
#define OP_addiu 	0x9
#define OP_slti 	0xa
#define OP_sltiu 	0xb
#define OP_andi 	0xc
#define OP_ori 		0xd
#define OP_xori 	0xe
#define OP_lui 		0xf

#define OP_lb 		0x20
#define OP_lh 		0x21
#define OP_lw 		0x23
#define OP_lbu 		0x24
#define OP_lhu		0x25
#define OP_sb 		0x28
#define OP_sh 		0x29
#define OP_sw 		0x2b


/*
 * These two opcodes specify that the instruction should be decoded
 * by looking at other fields of the instruction.
 */
#define OP_SPECIAL	0x0
#define OP_REGIMM	0x1


/* 
 *  Instructions with opcode == OP_SPECIAL, decoded by examining the
 *  func field
 */
#define FUNC_sll 	0x0
#define FUNC_srl 	0x2
#define FUNC_sra 	0x3
#define FUNC_sllv 	0x4
#define FUNC_srlv 	0x6
#define FUNC_srav 	0x7
#define FUNC_mfhi       0x10
#define FUNC_mthi       0x11
#define FUNC_mflo       0x12
#define FUNC_mtlo       0x13
#define FUNC_mult       0x18
#define FUNC_multu      0x19
#define FUNC_div        0x1a
#define FUNC_divu       0x1b
#define FUNC_add 	0x20
#define FUNC_addu 	0x21
#define FUNC_sub 	0x22
#define FUNC_subu 	0x23
#define FUNC_and 	0x24
#define FUNC_or 	0x25
#define FUNC_xor 	0x26
#define FUNC_nor 	0x27
#define FUNC_slt 	0x2a
#define FUNC_sltu 	0x2b
#define FUNC_jr 	0x8
#define FUNC_jalr 	0x9

#define FUNC_syscall	0x0c

/* 
 * Instructions with opcode == OP_REGIMM, decoded by examining the "rt" field 
*/

#define RT_bltz		0x0
#define RT_bgez		0x1
#define RT_bltzal	0x10
#define RT_bgezal	0x11

#endif /* __OPCODES_H__ */
