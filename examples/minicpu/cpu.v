//-------------------------------------------------------------------------
//
//  Copyright (c) 2008 Cornell University
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
//  $Id: cpu.v,v 1.7 2000/10/14 19:21:49 heinrich Exp $
//
//-------------------------------------------------------------------------

`include "mips.h"
`define mdtype_none  3'b000
`define mdtype_mult  3'b100
`define mdtype_multu 3'b101
`define mdtype_div   3'b110
`define mdtype_divu  3'b111

module	cpu
  (
   CLK,				// Clock signals
   MRST,				// Master reset
   Bus, Addr, Write, Read, Valid	// Memory interface
   );
   
   //--------------------------------------------------------------------
   
   input	{L} CLK;			// Clock 
   input	{L} MRST;			// Master reset
   input	Valid;			// Input from mem system on fills
   
   inout  [31:0] Bus;			// Data Bus between cpu & memory
   wire   [31:0] Bus;   
   output [31:0] Addr;			// Address Bus between cpu & memory
   wire   [31:0] Addr;
   output 	 Read;			// Bus Read
   wire 	 Read;
   output 	 Write;			// Bus Write
   wire 	 Write;
   
   /*--------------------------------------------------------------------
    Global Signals
    ---------------------------------------------------------------------*/
   // IF
   reg  [31:0] 	 PC, PC1, PC2, PC3, PC4;	// PC chain
   reg  [31:0] 	 IR1, IR2, IR3, IR4; 	// IR chain
   wire [31:0] 	 PCbr, PCinc, PCjmp;
   wire [4:0] 	 PCsel;			// Sel control for program counter
   wire [31:0] 	 PCoffset;		// Offset value for branches
   wire [31:0] 	 Iaddr;			// Address for instruction access
   wire [31:0] 	 Iin;			// Icache return value
   wire [25:0] 	 PCjump;			// Destination address for jumps
   wire 	 mem_pipeInhibit, pipeInhibit;		// whole pipe is stalled
   wire 	 mem_pcInhibit;		// When can PC change?
   reg       pcInhibit;
   
   // RD
   wire [4:0] 	 RSaddr;			// Source reg address specifier
   wire [4:0] 	 RTaddr;			// Target reg address specifier
   wire [4:0] 	 RDaddr;                 // Destination register address
   wire [31:0] 	 Imm;			// Immediate data
   wire [31:0] 	 RDbus;			// Destination bus
   wire 	 decodeStall;
   wire 	 instIsSyscall;
   reg 		 rInstIsSyscall;
   reg 		 rrInstIsSyscall;
   
   wire [31:0] 	 RS;	  // Source read port from reg
   wire [31:0] 	 RT;	  // Source read port form reg
   wire [1:0] 	 RSsel;	  // Bypassing select for RSbus
   wire [1:0] 	 RTsel;	  // Bypassing select for RTbus
   
   // EX
   wire [31:0] 	 preALUout;// pre ALU output register
   wire [31:0] 	 ALUout;   // ALU output register after MFLO/MFHI
   wire 	 QCResult; // Result from quick compare logic
   wire [5:0] 	 QCsel;
   wire [7:0] 	 ALUsel;
   wire 	 UseImm;
   wire [31:0] 	 HI;
   wire [31:0] 	 LO;
   wire          MD_ready;
   wire [2:0]    iMDtype;
   reg  [2:0]    currentMDtype;
   
   reg  [31:0] 	 RSbus;       // S source bus
   reg  [31:0] 	 RTbus;	      // T source bus
   reg  [4:0] 	 exRDaddr;    // Dest register in the EX stage
   reg  [31:0] 	 ImmBus;      // Saved Imediate bus for Pipeline
   wire [31:0] 	 RSbusMuxOut; // final forwarded RS bus
   wire [31:0] 	 RTbusMuxOut; // final forwarded RT bus
   
   // MEM
   reg  [31:0] 	 MAR, LMDR, SMDR;	// Mem address and data registers
   reg  [4:0] 	 memRDaddr;		// Dest register in the MEM stage
   wire [31:0] 	 {H} cacheOut;		// output of cache (loads)
   wire [31:0] 	 preLoadData;
   wire [31:0] 	 {H} loadData;		// final adjusted load output
   
   // WB
   wire [31:0] 	 WBreg;			// write back register
   wire [2:0] 	 WBsel;			// Stage 5 result select
   wire 	 WriteCLK;              	// Write clock	
   reg  [4:0] 	 wbRDaddr;		// Dest register in WB stage
   reg  [31:0] 	 SavedMAR;		// Saved MAR for Pipeline
   
   // Stats
   reg  [31:0] 	 numLoads;
   reg  [31:0] 	 numStores;
   reg  [31:0] 	 numDMisses;
   reg  [31:0] 	 numIMisses;
   reg  [31:0] 	 num_instructions;
   
   // Labels
   wire 		 {L} ReadLabel;
   wire			 {L} WriteLabel;
/*
   initial  begin
     $shm_open();
     $shm_probe(CPU,"AMC");
   end
*/   
   
   // FLOPs that reset the machine to a usable state, and then flow through 
   // the pipe.  The instruction register is flopped for each pipeline stage
   // and any control signals for that stage should come from that stages
   // version of the instruction register.
   always @(posedge CLK) begin
      if (MRST) begin
	 IR1 <= `TICK 32'b0;
	 IR2 <= `TICK 32'b0;
	 IR3 <= `TICK 32'b0;
	 IR4 <= `TICK 32'b0;
	 
	 exRDaddr  <= `TICK 5'b0;
	 memRDaddr <= `TICK 5'b0;
	 wbRDaddr  <= `TICK 5'b0;
      end
      else begin
	 if (decodeStall) begin
	    // NOPs in the EX phase
            IR2 <= `TICK 32'b0;
            exRDaddr  <= `TICK 5'b0;
	    
	    // Everything after EX goes through
	    // MEM stage
	    PC3 <= `TICK PC2;
	    IR3 <= `TICK IR2;
            SMDR <= `TICK RTbusMuxOut;
	    MAR  <= `TICK ALUout;
	    memRDaddr <= `TICK exRDaddr;
	    
	    // WB stage
	    PC4 <= `TICK PC3;
	    IR4 <= `TICK IR3;
	    LMDR <= `TICK loadData;
	    SavedMAR <= `TICK MAR;
	    wbRDaddr <= `TICK memRDaddr;
	 end
	 else if (~pipeInhibit) begin
	    // Normal, no cache miss case
	    
	    // Decode Stage
            PC1 <= `TICK Iaddr;
            IR1 <= `TICK Iin;
	    
	    // EX stage
            PC2 <= `TICK PC1;
            IR2 <= `TICK IR1;
	    RSbus <= `TICK RS;
	    RTbus <= `TICK RT;
	    ImmBus <= `TICK Imm; 
	    exRDaddr  <= `TICK RDaddr;
	    
	    // MEM stage
	    PC3 <= `TICK PC2;
	    IR3 <= `TICK IR2;
      SMDR <= `TICK RTbusMuxOut;
	    MAR  <= `TICK ALUout;
	    memRDaddr <= `TICK exRDaddr;
	    
	    // WB stage
	    PC4 <= `TICK PC3;
	    IR4 <= `TICK IR3;
	    LMDR <= `TICK loadData;
	    SavedMAR <= `TICK MAR;
	    wbRDaddr <= `TICK memRDaddr;
	 end
      end
   end
   
   /*--------------------------------------------------------------------
    Instruction Fetch Stage
    ---------------------------------------------------------------------*/
   ifcontr IFcontr 			// IF control logic
     (
      .I2 (IR2),
      .QC (QCResult),
      .PCsel (PCsel), 
      .PCoffset (PCoffset), 
      .PCjump (PCjump),
      .ReadLabel (ReadLabel),
      .WriteLabel (WriteLabel)
      ); 						
   
   /*--------------------------------------------------------------------
    PCsection: Update program counter and keep PC and Instruction register
    chains  
    ---------------------------------------------------------------------*/
   
   // Virtual instruction address taken from PC
   assign Iaddr = PC;
   assign PCbr  = PC2 + 4 + PCoffset;
   assign PCinc = PC + 32'h00000004;
   assign PCjmp = {PC2[31:28],PCjump,2'b0};
   
   // PC is now flopped on negedge CLK in an attempt to emulate the way
   // the MIPS R3000 shifts the IF stage by half a phase.  In the pipelined
   // model you can think of this like the PC gets flopped half-way through
   // the EX phase.  The value will either be the PC+4 or the branch target.
   
   always @(negedge CLK) begin
      if (MRST) begin
	 PC <= `TICK 32'hbfc00000;		// Reset vector
	 num_instructions <= `TICK 32'b0;
      end
      else if (~decodeStall & ~pcInhibit) begin
	 case(PCsel)		     
	   `select_pc_inc:      PC <= `TICK PCinc;
	   `select_pc_add:	PC <= `TICK PCbr;
	   `select_pc_jump:     PC <= `TICK PCjmp;
	   `select_pc_register: PC <= `TICK RSbusMuxOut;
	 endcase 
	 num_instructions <= `TICK num_instructions + 1'b1;
      end
   end
   
/*   
   always @(Iin) begin     // Mimic external memory
     $write("%d:pc=%h: ",$time, Iaddr);
     $disasm (Iin);
   end
*/   
   /*--------------------------------------------------------------------
    RF read stage  (RD) -- Read operands from register file
    ---------------------------------------------------------------------*/
   
   rf regfile		// Register File
     (	
	.WCLK	(WriteCLK),
	.RSaddr	(RSaddr), 
	.RTaddr	(RTaddr), 
	.RDaddr	(wbRDaddr), 
	.RS	(RS), 
	.RT	(RT),
	.RD	(RDbus)
	);
   
   rd RDcontr		// Register File and immediate control logic
     (
      .MRST (MRST),
      .I1	(IR1),
      .I2	(IR4),
      .RSaddr	(RSaddr),
      .RTaddr	(RTaddr),
      .RDaddr (RDaddr),
      .Imm	(Imm),
      .instIsSyscall (instIsSyscall),
      .ReadLabel (ReadLabel),
      .WriteLabel (WriteLabel)
      );
   
   // Register File Write Clock
   assign WriteCLK = (CLK == 1'b0);
   
   // -------------------------------------------------------------------
   // This section is code that detects syscall instructions and stalls
   // them in the Decode stage for 2 cycles.  This will become necessary
   // in our pipelined model so that our syscall emulation routines will
   // function properly.  Do not change this code unless you have a 
   // *really* good reason
   // -------------------------------------------------------------------

   always @(posedge CLK) begin
      if (~pipeInhibit) begin      
	 rInstIsSyscall <= `TICK instIsSyscall & ~pipeInhibit;
	 rrInstIsSyscall <= `TICK rInstIsSyscall;
      end
  	if (MD_ready) begin 
  		currentMDtype <= `TICK iMDtype;
  	end
  	pcInhibit <= `TICK pipeInhibit;
   end
   
   // Dstall and decodeStall are designed to be mutually exclusive
   // A Dstall can happen in the middle of a decode stall twice:
   // when the syscall is in RD and when the NOPs are in EX
   // in either case there can be a load or store in the MEM phase 
   // causing a cache miss
   
   assign decodeStall = (instIsSyscall | rInstIsSyscall) & ~rrInstIsSyscall & ~pipeInhibit;
   assign pipeInhibit = mem_pipeInhibit | (~MD_ready);
   
   /*--------------------------------------------------------------------
    Execute Stage (EX) -- Perform ALU or SHIFT Operation
    ---------------------------------------------------------------------*/
   // Bypassing Control select for RSbus
   // Bypassing control logic for S side
   bpcontr BPcontrS		
     (
      .addr (IR2[`rs]),
      .MemRDaddr (memRDaddr),
      .RDaddr (wbRDaddr),
      .BPsel (RSsel),
      .ReadLabel (ReadLabel),
      .WriteLabel (WriteLabel)
      );
   
   // Bypassing Control select for RTbus
   // Bypassing control logic for T side
   bpcontr BPcontrT		
     (
      .addr (IR2[`rt]),
      .MemRDaddr (memRDaddr),
      .RDaddr (wbRDaddr),
      .BPsel (RTsel),
      .ReadLabel (ReadLabel),
      .WriteLabel (WriteLabel)
      );   
   
   // Bypassing mux for RSbus
   
   assign 
	  RSbusMuxOut = (RSsel == `select_bp_reg) ? RSbus : 32'bz,
	  RSbusMuxOut = (RSsel == `select_bp_stage3) ? MAR : 32'bz,
	  RSbusMuxOut = (RSsel == `select_bp_stage4) ? RDbus : 32'bz;
   
   // Bypassing mux for RTbus
   
   assign 
	  RTbusMuxOut = (RTsel == `select_bp_reg) ? RTbus : 32'bz,
	  RTbusMuxOut = (RTsel == `select_bp_stage3) ? MAR : 32'bz,
	  RTbusMuxOut = (RTsel == `select_bp_stage4) ? RDbus : 32'bz;

ex EXcontr		// ALU control
(
	.I2		(IR2),
        .QCsel		(QCsel),
        .ALUsel		(ALUsel),
        .UseImm		(UseImm),
	.ReadLabel	(ReadLabel),
	.WriteLabel	(WriteLabel)
);

alu	ALU	
(
	.RSbus	(RSbusMuxOut),
	.RTbus	(RTbusMuxOut),
	.Imm	(ImmBus),
	.UseImm	(UseImm),
	.SEL	(ALUsel),
        .ALUout (preALUout),
	.ReadLabel	(ReadLabel),
	.WriteLabel	(WriteLabel)
);

// Quick compare logic
qc	QC	
(
	.RSbus	(RSbusMuxOut),
	.RTbus	(RTbusMuxOut),
	.QCsel	(QCsel),
        .Result (QCResult),
	.ReadLabel (ReadLabel),
	.WriteLabel (WriteLabel)
);
  // mult / div unit
  multdiv MD_A (
    .iCLK    (CLK),
    .iReset  (MRST),
    .iRS     (RSbusMuxOut),
    .iRT     (RTbusMuxOut),
    .iMDtype (iMDtype),
    .iHold   (1'b0),
    .iKill   (1'b0),
    .oLO     (LO),
    .oHI     (HI),
    .oReady  (MD_ready)
  );   
  
  assign iMDtype      = ((IR2[`op] == `SPECIAL) && (IR2[`function] == `MULT))  ? `mdtype_mult  :
  						((IR2[`op] == `SPECIAL) && (IR2[`function] == `MULTU)) ? `mdtype_multu :
						((IR2[`op] == `SPECIAL) && (IR2[`function] == `DIV))   ? `mdtype_div   :
						((IR2[`op] == `SPECIAL) && (IR2[`function] == `DIVU))  ? `mdtype_divu  : `mdtype_none;   
   
   // ALUout is preALUout unless a MFLO/MFHI instruction is in EX
   assign
	 ALUout = ((IR2[`op] == `SPECIAL) & (IR2[`function] == `MFLO)) ? LO : 32'bz,
	 ALUout = ((IR2[`op] == `SPECIAL) & (IR2[`function] == `MFHI)) ? HI : 32'bz,
	 ALUout = ((IR2[`op] != `SPECIAL) | ((IR2[`function] != `MFLO) & (IR2[`function] != `MFHI)))? preALUout : 32'bz;
   
   /*--------------------------------------------------------------------
    Memory Stage  (MEM) -- Access Data Memory
    ---------------------------------------------------------------------*/
   
   mem MEMcontr				// Memory access control
     (
      .CLK 	(CLK),
      .MRST 	(MRST),
      .I3	(IR3),
      .MAR    (MAR),
      .Valid (Valid),
      .SMDR	(SMDR),
      .Iaddr (Iaddr),
      .ReadLabel (ReadLabel),
      .WriteLabel (WriteLabel),
      
      .Bus	(Bus),
      
      .Read  (Read),
      .Write (Write),
      .Addr  (Addr),
      .cacheOut (cacheOut),
      .Iin (Iin),
      .pipeInhibit (mem_pipeInhibit),
      .pcInhibit (mem_pcInhibit)
      );
   
   
   // Handle sub-word loads
   
   wire [31:0] {H} preLoadDataLB, preLoadDataLH;
   
   assign      preLoadDataLB = (cacheOut >> (( ~MAR & 32'h3) << 3)) & 32'hff;
   assign      preLoadDataLH = (cacheOut >> (((~MAR >> 1 ) & 32'h1)  << 4)) & 32'hffff;
   assign      
	       loadData = (IR3[`op] == `LW)  ?  cacheOut : 32'bz,
	       loadData = (IR3[`op] == `LHU) ? (cacheOut >> ((( ~MAR >> 1 ) & 32'h1) << 4)) & 32'hffff : 32'bz,
	       loadData = (IR3[`op] == `LBU) ? (cacheOut >> ((~MAR & 32'h3) << 3)) & 32'hff : 32'bz,
	       loadData = (IR3[`op] == `LB)  ? {{24{preLoadDataLB[7]}}, preLoadDataLB[7:0]} : 32'bz,
	       loadData = (IR3[`op] == `LH)  ? {{16{preLoadDataLH[15]}},preLoadDataLH[15:0]}:32'bz;
   
   
   /*--------------------------------------------------------------------
    Writeback Stage (WB) -- Write data back to register file
    ---------------------------------------------------------------------*/
   
   wb WBcontr			// Register write back control
     (
      .I4	(IR4),
      .WBsel	(WBsel),
      .ReadLabel (ReadLabel),
      .WriteLabel (WriteLabel)
      );
   
   
   assign      RDbus = WBreg;  // Drive RDbus with contents of WBreg
   
   assign      
	       WBreg = (WBsel == `select_wb_load) ? LMDR : 32'bz,
	       WBreg = (WBsel == `select_wb_link) ? PC4 + 32'h8 : 32'bz,
	       WBreg = ((WBsel != `select_wb_load) & (WBsel != `select_wb_link)) ? SavedMAR : 32'bz;
   
endmodule

