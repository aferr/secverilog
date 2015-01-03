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
//  $Id: ex.v,v 1.2 1999/10/18 17:58:51 heinrich Exp $
//
//-------------------------------------------------------------------------

`include "mips.h"

module ex (I2, ALUsel, QCsel, UseImm, ReadLabel, WriteLabel);

input	[31:0]	I2;	// Stage 3 instruction
input 		 ReadLabel;
input		 WriteLabel;

output	[7:0]	ALUsel;		
reg     [7:0]	ALUsel;	// ALU operation select
output	[5:0]	QCsel;		
reg     [5:0]	QCsel;	// Quick compare operation select
output		UseImm;		
reg 		UseImm;	// Use the Immediate data

/*-------------------------------------------------------------------
 As the name implies, this is the EX pipeline stage (part of it!).

 This logic examines the current instruction, if the instruction is
 an ALU instruction it selects the proper ALU function.  If the 
 instruction is a LD/ST then it computes the effective address in the
 ALU stage and selects the add operation.  If one of the ALU inputs
 is immediate data, then the immediate path is selected.  
---------------------------------------------------------------------*/

always @(I2) begin
   // Load, store and imm operations all select
   UseImm = (I2[`op] == `LW)   | (I2[`op] == `SW)    |	
            (I2[`op] == `LBU)  | (I2[`op] == `LB)    | 
            (I2[`op] == `LHU)  | (I2[`op] == `LH)    |
            (I2[`op] == `SH)   | (I2[`op] == `SB)    | 
            (I2[`op] == `ADDI) | (I2[`op] == `ADDIU) |
	    // the immediate path as the target operand.
	    (I2[`op] == `SLTI) | (I2[`op] == `SLTIU) |
   	    (I2[`op] == `ANDI) | (I2[`op] == `ORI)   |
	    (I2[`op] == `XORI) | (I2[`op] == `LUI)   |
	    ((I2[`op] == `SPECIAL) && 
	    ((I2[`function] == `SLL) | (I2[`function] == `SRL) |
	     (I2[`function] == `SRA)) );

   // Compute ALU operation select controls
   casex({I2[`op], I2[`function]})

      {`SPECIAL, `ADD	}: ALUsel = `select_alu_add;
      {`SPECIAL, `ADDU	}: ALUsel = `select_alu_add;
      {`SPECIAL, `SUB	}: ALUsel = `select_alu_sub;
      {`SPECIAL, `SUBU	}: ALUsel = `select_alu_sub;
      {`SPECIAL, `SLT	}: ALUsel = `select_alu_slt;
      {`SPECIAL, `SLTU	}: ALUsel = `select_alu_sltu;
      {`SPECIAL, `AND	}: ALUsel = `select_alu_and;
      {`SPECIAL, `OR	}: ALUsel = `select_alu_or;
      {`SPECIAL, `XOR	}: ALUsel = `select_alu_xor;
      {`SPECIAL, `NOR	}: ALUsel = `select_alu_nor;
      {`SPECIAL, `SRL   }: ALUsel = `select_alu_srl;
      {`SPECIAL, `SRA	}: ALUsel = `select_alu_sra;
      {`SPECIAL, `SLL	}: ALUsel = `select_alu_sll;
      {`SPECIAL, `SLLV	}: ALUsel = `select_alu_sll;
      {`SPECIAL, `SRLV  }: ALUsel = `select_alu_srl;
      {`SPECIAL, `SRAV	}: ALUsel = `select_alu_sra;

      {`ADDI,	 `dc6	}: ALUsel = `select_alu_add;
      {`ADDIU,	 `dc6	}: ALUsel = `select_alu_add;
      {`SLTI,	 `dc6	}: ALUsel = `select_alu_slt;
      {`SLTIU,	 `dc6	}: ALUsel = `select_alu_sltu;
      {`ANDI,	 `dc6	}: ALUsel = `select_alu_and;
      {`ORI,	 `dc6	}: ALUsel = `select_alu_or;
      {`XORI,	 `dc6	}: ALUsel = `select_alu_xor;

      {`LUI,	 `dc6	}: ALUsel = `select_alu_or;

      {`LW,	 `dc6	}: ALUsel = `select_alu_add;
      {`LBU,	 `dc6	}: ALUsel = `select_alu_add;
      {`LB,	 `dc6	}: ALUsel = `select_alu_add;
      {`LH,      `dc6   }: ALUsel = `select_alu_add;  
      {`LHU,     `dc6   }: ALUsel = `select_alu_add;  
      {`SW,	 `dc6	}: ALUsel = `select_alu_add;
      {`SH,      `dc6   }: ALUsel = `select_alu_add;
      {`SB,	 `dc6	}: ALUsel = `select_alu_add;

      default:		   ALUsel = `dc8;
   endcase
end

//--------------------------------------------------------------------
// this code sets the mux control for the quick comparator logic in qc.v
//--------------------------------------------------------------------
always @(I2) begin	
   // Compute quick compare select controls
   casex({I2[`op], I2[`rt]})
      {`BEQ,	`dc5	}: QCsel = `select_qc_eq;
      {`BNE,	`dc5	}: QCsel = `select_qc_ne;
      {`BLEZ,	`dc5	}: QCsel = `select_qc_lez;
      {`BGTZ,	`dc5	}: QCsel = `select_qc_gtz;
      {`REGIMM,	`BLTZ   }: QCsel = `select_qc_ltz;
      {`REGIMM,	`BGEZ   }: QCsel = `select_qc_gez;
      {`REGIMM, `BGEZAL }: QCsel = `select_qc_gez;
      {`REGIMM, `BLTZAL }: QCsel = `select_qc_ltz;
      default:		   QCsel = `dc6;
   endcase
end

//--------------------------------------------------------------------
// This code handles syscall emulation and should not be changed
// unless you have a death wish.
//--------------------------------------------------------------------

`ifdef NOSYNTH
      
`include "sysfunc.h"

always @(I2) begin
   casex({I2[`op], I2[`function]})
      {`SPECIAL, `SYSCALL}: syscall;
   endcase
end   
`endif
endmodule

