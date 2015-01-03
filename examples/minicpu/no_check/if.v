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
//  $Id: if.v,v 1.2 1999/10/13 19:28:11 heinrich Exp $
//
//-------------------------------------------------------------------------

`include "mips.h"

module ifcontr (I2, QC, PCsel, PCoffset, PCjump, ReadLabel, WriteLabel);
   
   input		QC;		// Quick Compare result for branches
   input	[31:0]	I2;		// Instruction to be decoded
   input 			ReadLabel;
   input			WriteLabel;
   
   output [4:0] 	PCsel;		
   reg    [4:0]		PCsel;		// Select control for program counter
   
   output [31:0] 	PCoffset;
   reg    [31:0]	PCoffset;	// Offset value for branches
   
   output [25:0] 	PCjump;		
   reg    [25:0]	PCjump;		// Destination address for jumps
   
   //--------------------------------------------------------------------
   // This module seems like a misnomure because the instruction fetch 
   // control logic (if.v) actually takes place in the EX phase.  This
   // make sense when you think about the pipeline because branches are
   // resolved in the EX phase, and based on the outcome of the branch
   // I either select PC+4 or the PC+4+branchOffset.
   //--------------------------------------------------------------------
   
   reg 			takeBranch; // Compute whether a branch should be taken
   
   always @(I2 or QC) begin
      casex ({I2[`op], I2[`rt], QC})
	
	{`BEQ,	`dc5,	`true	}:	takeBranch = `true;
	{`BNE,	`dc5,	`true	}:	takeBranch = `true;
	{`BLEZ,	`dc5,	`true	}:	takeBranch = `true;
	{`BGTZ,	`dc5,	`true	}:	takeBranch = `true;
	{`REGIMM,`BLTZ,	`true	}:	takeBranch = `true;
	{`REGIMM,`BGEZ,	`true	}:	takeBranch = `true;
	{`REGIMM,`BGEZAL,`true	}:	takeBranch = `true;
	{`REGIMM,`BLTZAL,`true  }:      takeBranch = `true;
	default:   takeBranch = `false;
	
      endcase
   end
   
//--------------------------------------------------------------------

// Compute program counter select controls
   
always @(I2 or takeBranch) begin
   casex ({I2[`op], I2[`rt], I2[`function], takeBranch})

     // Select jump address as target
     {`J,	 `dc5,	`dc6,	`dc	}: PCsel = `select_pc_jump;
     {`JAL,	 `dc5,	`dc6,	`dc	}: PCsel = `select_pc_jump;

     // Select register value as target
     {`SPECIAL, `dc5,	`JR,	`dc	}: PCsel = `select_pc_register;
     {`SPECIAL, `dc5,	`JALR,	`dc	}: PCsel = `select_pc_register;

     // Select branch (PC + offset) as target
     {`BEQ,	 `dc5,	`dc6,	`true	}: PCsel = `select_pc_add;	
     {`BNE,	 `dc5,	`dc6,	`true	}: PCsel = `select_pc_add;
     {`BLEZ,	 `dc5,	`dc6,	`true	}: PCsel = `select_pc_add;
     {`BGTZ,	 `dc5,	`dc6,	`true	}: PCsel = `select_pc_add;
     {`REGIMM,	 `BLTZ,	`dc6,	`true	}: PCsel = `select_pc_add;
     {`REGIMM,	 `BGEZ,	`dc6,	`true	}: PCsel = `select_pc_add;
     // Added to support glibc
     {`REGIMM,   `BGEZAL,`dc6,  `true   }: PCsel = `select_pc_add;
     {`REGIMM,   `BLTZAL,`dc6,  `true   }: PCsel = `select_pc_add;

     // Select exception/reset vector as target
     // Otherwise, select incremented PC
     default:	PCsel = `select_pc_inc;

   endcase 
end 

//--------------------------------------------------------------------

// Compute target for branch and jump instructions
always @(I2) begin
    casex(I2[`op])
      // Jump instructions use 26 bit `target field
      `J	: PCjump = I2[`target];
      `JAL	: PCjump = I2[`target];
      default	: PCjump = `dc32;
    endcase

    casex({I2[`op], I2[`rt]})
      // Shift left twice and sign extend
      {`BEQ,    `dc5	}: PCoffset = {{14{I2[15]}}, I2[`immediate], 2'b0};
      {`BNE,	`dc5	}: PCoffset = {{14{I2[15]}}, I2[`immediate], 2'b0};
      {`BLEZ,	`dc5	}: PCoffset = {{14{I2[15]}}, I2[`immediate], 2'b0};
      {`BGTZ,	`dc5	}: PCoffset = {{14{I2[15]}}, I2[`immediate], 2'b0};
      {`REGIMM,	`BLTZ	}: PCoffset = {{14{I2[15]}}, I2[`immediate], 2'b0};
      {`REGIMM,	`BGEZ	}: PCoffset = {{14{I2[15]}}, I2[`immediate], 2'b0};
      {`REGIMM, `BGEZAL }: PCoffset = {{14{I2[15]}}, I2[`immediate], 2'b0};
      {`REGIMM, `BLTZAL }: PCoffset = {{14{I2[15]}}, I2[`immediate], 2'b0};
      default:		   PCoffset = `dc32;

    endcase
end

//--------------------------------------------------------------------

endmodule	
