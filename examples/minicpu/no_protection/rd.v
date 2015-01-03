//-------------------------------------------------------------------------
//
//  Copyright (c) 1999 Cornell University
//  Computer Systems Laboratory
//  Cornell University, Ithaca, NY 14853
//  All Rights Reserved
//
//  Permission to use, copy, modify, and distribute this software
//  and its documentation for any purpose and without fee is hereby
//  granted, provided that the above copyright notice appear in all
//  copies. Cornell University makes no representations
//  about the suitability of this software for any purpose. It is
//  provided "as is" without express or implied warranty. Export of this
//  software outside of the United States of America may require an
//  export license.
//
//  $Id: rd.v,v 1.2 1999/10/13 19:28:12 heinrich Exp $
//
//-------------------------------------------------------------------------

`include "mips.h"

module rd (I1, RSaddr, RTaddr, RDaddr, Imm, instIsSyscall);
   
   input  [31:0]	I1;	// Stage 2 instruction
   
   output [4:0] 	RSaddr;		
   reg    [4:0]		RSaddr;	// Source register address specifier
   output [4:0] 	RTaddr;	
   reg    [4:0]		RTaddr;	// Target register address specifier
   output [4:0] 	RDaddr;
   reg    [4:0]		RDaddr; // Destination register address
   output [31:0] 	Imm;	
   reg    [31:0]	Imm;	// Immediate data
   output		instIsSyscall;
   reg 			instIsSyscall;
   
   //--------------------------------------------------------------------
   // This is the Decode phase of the pipeline.  It just simply sets the RS,
   // RT, and RD register specifiers, sets the Immediate bus to the immediate
   // field of the instruction and checks for illegal instructions
   //--------------------------------------------------------------------
   
   integer 		instOK;
   
   always @(I1) begin
      // Always take rs and rt from same place
      RSaddr = I1[`rs];	
      RTaddr = I1[`rt];
      
      // Decode destination register number. If the operation does 
      // not write to the register file, set zero.
      casex ({I1[`op], I1[`function]})
	// Load result goes to `rt register
	{`LW,      `dc6   }: RDaddr = I1[`rt];
	{`LHU,     `dc6   }: RDaddr = I1[`rt];
	{`LH,      `dc6   }: RDaddr = I1[`rt];
	{`LBU,     `dc6   }: RDaddr = I1[`rt];
	{`LB,      `dc6   }: RDaddr = I1[`rt];
	
	// Immediate operation results go to `rt
	{`ADDI,    `dc6   }: RDaddr = I1[`rt];
	{`ADDIU,   `dc6   }: RDaddr = I1[`rt];
	{`SLTI,    `dc6   }: RDaddr = I1[`rt];
	{`SLTIU,   `dc6   }: RDaddr = I1[`rt];
	{`ANDI,    `dc6   }: RDaddr = I1[`rt];
	{`ORI,     `dc6   }: RDaddr = I1[`rt];
	{`XORI,    `dc6   }: RDaddr = I1[`rt];
	{`LUI,     `dc6   }: RDaddr = I1[`rt];
	
	// ALU operation results go to `rd register
	{`SPECIAL, `ADD   }: RDaddr = I1[`rd];
	{`SPECIAL, `ADDU  }: RDaddr = I1[`rd];
	{`SPECIAL, `SUB   }: RDaddr = I1[`rd];
	{`SPECIAL, `SUBU  }: RDaddr = I1[`rd];
	{`SPECIAL, `SLT   }: RDaddr = I1[`rd];
	{`SPECIAL, `SLTU  }: RDaddr = I1[`rd];
	{`SPECIAL, `AND   }: RDaddr = I1[`rd];  
	{`SPECIAL, `OR    }: RDaddr = I1[`rd];
	{`SPECIAL, `XOR   }: RDaddr = I1[`rd];
	{`SPECIAL, `NOR   }: RDaddr = I1[`rd];
	
	// Note, other shift decode to be added...
	// Shift operations go to `rd register
	{`SPECIAL, `SLL   }: RDaddr = I1[`rd];
	{`SPECIAL, `SRL   }: RDaddr = I1[`rd];
	{`SPECIAL, `SRA   }: RDaddr = I1[`rd];
	{`SPECIAL, `SLLV  }: RDaddr = I1[`rd];
	{`SPECIAL, `SRLV  }: RDaddr = I1[`rd];
	{`SPECIAL, `SRAV  }: RDaddr = I1[`rd];
	
	// Link register is R31
	{`JAL,     `dc6   }: RDaddr = `r31;   
	{`SPECIAL, `JALR  }: RDaddr = I1[`rd];

	// MFHI and MFLO
	{`SPECIAL, `MFLO  }: RDaddr = I1[`rd];
	{`SPECIAL, `MFHI  }: RDaddr = I1[`rd];
	
	// All other instruction results go to `r0
	default            : RDaddr = `r0;
      endcase
      
      
      // Compute value for 32 bit immediate data
      casex(I1[`op])

	// Sign extend for memory access operations
	`LW	: Imm = {{16{I1[15]}}, I1[`immediate]};	
	`LHU    : Imm = {{16{I1[15]}}, I1[`immediate]};
	`LH     : Imm = {{16{I1[15]}}, I1[`immediate]};
	`LBU	: Imm = {{16{I1[15]}}, I1[`immediate]};	
	`LB	: Imm = {{16{I1[15]}}, I1[`immediate]};	
	`SW	: Imm = {{16{I1[15]}}, I1[`immediate]};
	`SH     : Imm = {{16{I1[15]}}, I1[`immediate]};
	`SB	: Imm = {{16{I1[15]}}, I1[`immediate]};
	
	// ALU Operations that sign extend immediate
	`ADDI	: Imm = {{16{I1[15]}}, I1[`immediate]};
	`ADDIU	: Imm = {{16{I1[15]}}, I1[`immediate]};
	`SLTI	: Imm = {{16{I1[15]}}, I1[`immediate]};
	`SLTIU	: Imm = {{16{I1[15]}}, I1[`immediate]};
	
	// ALU Operations that zero extend immediate
	`ANDI	: Imm = {16'b0, I1[`immediate]};	
	`ORI	: Imm = {16'b0, I1[`immediate]};
	`XORI	: Imm = {16'b0, I1[`immediate]};
	`SLL    : Imm = {16'b0, I1[`immediate]};
	`SRL    : Imm = {16'b0, I1[`immediate]};

	// LUI fills low order bits with zeros
	`LUI	: Imm = {I1[`immediate], 16'b0};
	
	default	: Imm = `dc32;
      endcase
      
      // Check for illegal instructions (good debugging feature)
      casex({I1[`op], I1[`function], I1[`rt]})
	{`SPECIAL, `ADD,     `dc5 }: instOK = 1;
	{`SPECIAL, `ADDU,    `dc5 }: instOK = 1;
	{`SPECIAL, `SUB,     `dc5 }: instOK = 1;
	{`SPECIAL, `SUBU,    `dc5 }: instOK = 1;
	{`SPECIAL, `SLT,     `dc5 }: instOK = 1;
	{`SPECIAL, `SLTU,    `dc5 }: instOK = 1;
	{`SPECIAL, `AND,     `dc5 }: instOK = 1;
	{`SPECIAL, `OR,      `dc5 }: instOK = 1;
	{`SPECIAL, `XOR,     `dc5 }: instOK = 1;
	{`SPECIAL, `NOR,     `dc5 }: instOK = 1;
	{`SPECIAL, `SRL,     `dc5 }: instOK = 1;
	{`SPECIAL, `SRA,     `dc5 }: instOK = 1;
	{`SPECIAL, `SLL,     `dc5 }: instOK = 1;
	{`SPECIAL, `SLLV,    `dc5 }: instOK = 1;
	{`SPECIAL, `SRLV,    `dc5 }: instOK = 1;
	{`SPECIAL, `SRAV,    `dc5 }: instOK = 1;
	{`SPECIAL, `JR,      `dc5 }: instOK = 1;
	{`SPECIAL, `JALR,    `dc5 }: instOK = 1;
	{`SPECIAL, `SYSCALL, `dc5 }: instOK = 1;
	{`SPECIAL, `BREAK,   `dc5 }: instOK = 1;
	
	{`SPECIAL, `MULT,    `dc5 }: instOK = 1;
	{`SPECIAL, `MULTU,   `dc5 }: instOK = 1;
	{`SPECIAL, `DIV,     `dc5 }: instOK = 1;
	{`SPECIAL, `DIVU,    `dc5 }: instOK = 1;
	{`SPECIAL, `MFHI,    `dc5 }: instOK = 1;
	{`SPECIAL, `MFLO,    `dc5 }: instOK = 1;
	
	{`REGIMM, `dc6, `BLTZ}: instOK = 1;
	{`REGIMM, `dc6, `BGEZ}: instOK = 1;

	// Added the following 2 instructions to support glibc
	{`REGIMM, `dc6, `BGEZAL}: instOK = 1;
	{`REGIMM, `dc6, `BLTZAL}: instOK = 1;
	
	// Branch likely instructions are not supported
	// Trap instructions are not implemented
	
	{`ADDI,	 `dc6, `dc5 }: instOK = 1;
	{`ADDIU, `dc6, `dc5 }: instOK = 1;
	{`SLTI,	 `dc6, `dc5 }: instOK = 1;
	{`SLTIU, `dc6, `dc5 }: instOK = 1;
	{`ANDI,	 `dc6, `dc5 }: instOK = 1;
	{`ORI,	 `dc6, `dc5 }: instOK = 1;
	{`XORI,	 `dc6, `dc5 }: instOK = 1;
	{`LUI,	 `dc6, `dc5 }: instOK = 1;
	{`LW,	 `dc6, `dc5 }: instOK = 1;
	{`LHU,   `dc6, `dc5 }: instOK = 1;
	{`LH,    `dc6, `dc5 }: instOK = 1;
	{`LBU,	 `dc6, `dc5 }: instOK = 1;
	{`LB,	 `dc6, `dc5 }: instOK = 1;
	{`SW,	 `dc6, `dc5 }: instOK = 1;
	{`SWL,   `dc6, `dc5 }: instOK = 1;
	{`SH,    `dc6, `dc5 }: instOK = 1;
	{`SB,	 `dc6, `dc5 }: instOK = 1;
	{`J,	 `dc6, `dc5 }: instOK = 1;
	{`JAL,	 `dc6, `dc5 }: instOK = 1;
	{`BNE,	 `dc6, `dc5 }: instOK = 1;
	{`BEQ,	 `dc6, `dc5 }: instOK = 1;
	{`BLEZ,	 `dc6, `dc5 }: instOK = 1;
	{`BGTZ,	 `dc6, `dc5 }: instOK = 1;
	
	// These are passed thru as NOPs so that real
	// program may run.  We don't implement FP or coprocessor
	// instructions right now
	{`LWC1,	 `dc6, `dc5 }: instOK = 1;
	{`SWC1,	 `dc6, `dc5 }: instOK = 1;
	{`COP1,	 `dc6, `dc5 }: instOK = 1;
	
	default:
	  begin
             $display("%d:Error: Illegal Instruction!\n", $time);
             $display("Instruction is: ");
	     $disasm(I1);
	     $finish;
	  end
      endcase
      
      // Special handling for syscall instructions.
      // In the pipelined model we need to stall for 2 cycles
      // so that our syscall emulation routines will copy the right
      // values from the register file
      
      casex({I1[`op], I1[`function], I1[`rt]})
	{`SPECIAL, `SYSCALL, `dc5 }: instIsSyscall = 1'b1;
	default: instIsSyscall = 1'b0;
      endcase
   end
   
endmodule
