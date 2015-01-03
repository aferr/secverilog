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
//  $Id: alu.v,v 1.2 1999/10/18 17:58:51 heinrich Exp $
//
//-------------------------------------------------------------------------

`include "mips.h"

module alu (RSbus, RTbus, Imm, UseImm, SEL, ALUout, ReadLabel, WriteLabel);
input	[31:0]	RSbus;			// rs operand input
input 	[31:0]	RTbus;			// rt operand input
input 	[31:0]	Imm;			// immediate operand input
input		UseImm;			// Use immediate operand
input	[7:0]	SEL;			// Operation select
input		{L} ReadLabel;
input		{L} WriteLabel;
output	[31:0]	ALUout;			// ALU output
reg	[31:0]	Y, ALUout;
reg     [4:0] 	SA;		        // shift amount

//--------------------------------------------------------------------

// Perform ALU operation
always @(RSbus or RTbus or Imm or SEL or UseImm) begin
   // mux in the right operands
   Y = (UseImm) ? Imm : ((SEL[7] == 1'b1) ? RSbus : RTbus);
   SA = (UseImm) ? Imm[10:6] : RSbus[4:0];
   // Instructions Supported
   case (SEL)
      `select_alu_add:  ALUout = RSbus + Y;	// ADD, ADDI, ADDU, ADDIU
      `select_alu_and:	ALUout = RSbus & Y;	// AND, ANDI
      `select_alu_xor:	ALUout = RSbus ^ Y;	// XOR, XORI
      `select_alu_or:   ALUout = RSbus | Y;	// OR, ORI
      `select_alu_nor:	ALUout = ~(RSbus | Y);	// NOR
      `select_alu_sub:	ALUout = RSbus - Y;	// SUB, SUBU
						// SLTU, SLTIU
      `select_alu_sltu:	ALUout = ({1'b0,RSbus} < {1'b0,Y}) ? 1 : 0;
      `select_alu_slt:	ALUout = (RSbus[31] != Y[31] ? RSbus[31] : ((RSbus < Y) ? 1 : 0)); // SLT, SLTI
      `select_alu_sra:  ALUout = {{32{RTbus[31]}},RTbus} >> SA;
      `select_alu_srl:  ALUout = RTbus >> SA; // SRL
      `select_alu_sll:  ALUout = RTbus << SA; // SLL
     default:		ALUout = `undefined;			// Undefined
   endcase

   //$display("%d:Sbus=%h, TBus=%h, Imm=%h, Sel=%b, UseImm=%b, ALUout=%h\n", $time, RSbus, RTbus, Imm, SEL, UseImm, ALUout);
  end

//-------------------------------------------------------------------

endmodule
