
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
//  $Id: mem.v,v 1.8 2000/10/14 19:21:49 heinrich Exp $
//
//-------------------------------------------------------------------------

`include "mips.h"
`include "cache.h"
   
module mem (CLK, I3, MRST, MAR, Valid, SMDR, Iaddr, ReadLabel, WriteLabel, Bus, Read, Write, Addr, cacheOut, Iin, pipeInhibit, pcInhibit);
   
   // clock and reset
   input		{L} CLK;
   input		{L} MRST;
   input		{L} ReadLabel;
   input		{L} WriteLabel;

   // signals from the processor pipeline
   input [31:0] 	I3;	// Stage 4 instruction
   input [31:0] 	MAR;
   input [31:0] 	SMDR;
   input [31:0] 	Iaddr;

   // signals to the processor pipeline
   output [31:0] 	cacheOut;
   wire [31:0] 		{H} cacheOut;
   output [31:0] 	Iin;
   wire [31:0] 		Iin;
   output		pcInhibit;
   reg  		pcInhibit;
   output		pipeInhibit;
   wire 		pipeInhibit;
   
   // Memory bus interface
   input		Valid;
   inout [31:0] 	{BusPar Write} Bus;
   output		Read;		
   wire			Read;
   output		Write;	
   wire			Write;
   output [31:0] 	Addr;
   wire [31:0] 		Addr;

   //--------------------------------------------------------------------
   // As the name implies this is the control logic for the MEM pipe stage.
   // The Dread indication is set if the instruction in MEM is some kind of
   // load.  On a store it sets the Dwrite flag and also the Dsize variable
   // to the size of the store (byte, half-word, word).  The store logic is
   // handled external to the chip,in mips.v
   //--------------------------------------------------------------------
   
   //
   // I$ FSM states
   //
   parameter IFSM_IDLE      = 2'd0;
   parameter IFSM_WAITMEM   = 2'd1;
   parameter IFSM_REFILL    = 2'd2;

   //
   // D$ FSM states
   //
   parameter DFSM_IDLE      = 3'd0;
   parameter DFSM_STOREHIT  = 3'd1;
   parameter DFSM_WRITEBACK = 3'd2;
   parameter DFSM_WAITMEM   = 3'd3;
   parameter DFSM_REFILL    = 3'd4;

   // FSM
   reg [1:0]			iFsmState; 
   reg [2:0]			dFsmState; 

   // Word offset
   reg [`I_WO_WIDTH-1:0]	iOffset;
   reg [`D_WO_WIDTH:0]	dOffset;
   reg [`D_WO_WIDTH:0]	nDOffset;

   // Memory bus signals
   reg 				BusSel;

   wire 			iMemValid;
   wire [31:0] 			iMemAddr;
   reg 				iMemRead;

   wire 			dMemValid;
   reg [31:0] 			dMemAddr;
   reg 				dMemRead;
   wire [31:0]			{H} dMemBus;
   reg 				dMemWrite;

   // I$ control signals
   wire				iHit;
   wire 			{H} iHitNaive;
   wire				iHit0;
   wire				iHit1;
   wire				{H} iHit2;
   wire				{H} iHit3;
   wire				iStall;
   reg [31:0]			{L} iCacheOut;

   // D$ control signals
   wire				dHit;
   wire				{H} dHitNaive;
   wire				dHit0;
   wire				dHit1;
   wire				{H} dHit2;
   wire				{H} dHit3;
   wire 			dStall;
   reg [1:0]			Dsize;
   reg				isLoad;
   reg				isStore;
   reg [31:0]			rMAR;
 
   // These wires are for performing sub-word stores
   wire [4:0] 		  	sa;
   wire [31:0] 		  	mask;
   
   //--------------------------------------------------------------------
   //
   // Instantiation memory modules
   //
   //--------------------------------------------------------------------
	
   reg [1:0]				 iWay;
   // Instruction cache tag RAM
   wire [`I_TAG_WIDTH-1:0]   iTagRamOutLow[0:1];
   wire [`I_TAG_WIDTH-1:0]   {H} iTagRamOutHigh[0:1];
   wire [`I_INDEX_WIDTH-1:0] iTagRamIndex;
   wire [`I_TAG_WIDTH-1:0]   iTagRamIn;
   reg 			     iTagRamWe;
      
   //spram #(`I_TAG_WIDTH, `I_INDEX_WIDTH, (2<<`I_INDEX_WIDTH)) ic_tmem 
   itram ic_tmem
     (
      .clk (CLK),
      //.addr (iTagRamIndex),
      .index (iTagRamIndex),
      .way (iWay),
      .din (iTagRamIn),
      .dout0 (iTagRamOutLow[0]),
      .dout1 (iTagRamOutLow[1]),
      .dout2 (iTagRamOutHigh[0]),
      .dout3 (iTagRamOutHigh[1]),
      .we (iTagRamWe),
      .en (1'b1)

      );

   // Instruction cache state RAM
   wire [1:0] 	             iStateRamOutLow[0:1];
   wire [1:0] 	             {H} iStateRamOutHigh[0:1];
   wire [`I_INDEX_WIDTH-1:0] iStateRamIndex;
   wire [1:0] 		     iStateRamIn;
   reg 			     iStateRamWe;
      
   //spram #(2, `I_INDEX_WIDTH, (2<<`I_INDEX_WIDTH)) ic_smem 
   isram ic_smem
     (
      .clk (CLK),
      //.addr (iStateRamIndex),
      .index (iStateRamIndex),
      .way (iWay),
      .din (iStateRamIn),
      .dout0 (iStateRamOutLow[0]),
      .dout1 (iStateRamOutLow[1]),
      .dout2 (iStateRamOutHigh[0]),
      .dout3 (iStateRamOutHigh[1]),
      .we (iStateRamWe),
      .en (1'b1)

      );
   
   // Instruction cache data RAM 
   wire [31:0] 	             iDataRamOutLow[0:1];
   wire [31:0] 	             {H} iDataRamOutHigh[0:1];
   wire [31:0]				 iDataRamMuxOut;
   wire [`I_INDEX_WIDTH-1:0] iDataRamIndex;
   wire [`D_WO_WIDTH-1:0]    iDataRamOffset;
   reg [31:0] 		     iDataRamIn;
   reg 			     iDataRamWe;
      
   //spram #(32, (`I_INDEX_WIDTH+`I_WO_WIDTH), (2<<(`I_INDEX_WIDTH+`I_WO_WIDTH))) ic_dmem 
   idram ic_dmem
     (
      .clk (CLK),
      //.addr ({iDataRamIndex,iDataRamOffset}),
      .index (iDataRamIndex),
      .way (iWay),
      .offset (iDataRamOffset),
      .din (iDataRamIn),
      .dout0 (iDataRamOutLow[0]),
      .dout1 (iDataRamOutLow[1]),
      .dout2 (iDataRamOutHigh[0]),
      .dout3 (iDataRamOutHigh[1]),
      .we (iDataRamWe),
      .en (1'b1)

      );

   wire [1:0] dReadWay;          // specify which way to replace
   reg [1:0]  {Way dWriteWay} dWriteWay;
   wire [1:0]  {Way dStateWay} dStateWay;
//    wire [1:0] {Way dWay} dWay;
   
   // Data cache tag RAM 
   wire [`D_TAG_WIDTH-1:0]   dTagRamOutLow[0:1];
   wire [`D_TAG_WIDTH-1:0]   {H} dTagRamOutHigh[0:1];
   wire [`D_INDEX_WIDTH-1:0] dTagRamIndex;
   wire [`D_TAG_WIDTH-1:0]   dTagRamIn;
   reg 			     dTagRamWe;
      
   //spram #(`D_TAG_WIDTH, `D_INDEX_WIDTH, (2<<`D_INDEX_WIDTH)) dc_tmem 
   dtram dc_tmem
     (
      .clk (CLK),
      //.addr (dTagRamIndex),
      .index (dTagRamIndex),
      .way (dWriteWay),
      .din (dTagRamIn),
      .dout0 (dTagRamOutLow[0]),
      .dout1 (dTagRamOutLow[1]),
      .dout2 (dTagRamOutHigh[0]),
      .dout3 (dTagRamOutHigh[1]),
      .we (dTagRamWe),
      .en (1'b1)

      );

   // Data cache state RAM
   wire [1:0] 	             dStateRamOutLow[0:1];
   wire [1:0]		     {H} dStateRamOutHigh[0:1];
   wire [`D_INDEX_WIDTH-1:0] dStateRamIndex;
   reg [1:0] 		     {Way dStateWay} dStateRamIn;
   reg 			     {Way dStateWay} dStateRamWe;
      
   //spram #(2, `D_INDEX_WIDTH, (2<<`D_INDEX_WIDTH)) dc_smem 
   dsram dc_smem 
     (
      .clk (CLK),
      //.addr (dStateRamIndex),
      .index (dStateRamIndex),
      .way (dStateWay),
      .din (dStateRamIn),
      .dout0 (dStateRamOutLow[0]),
      .dout1 (dStateRamOutLow[1]),
      .dout2 (dStateRamOutHigh[0]),
      .dout3 (dStateRamOutHigh[1]),
      .we (dStateRamWe),
      .en (1'b1)

      );

   // Data cache data RAM
   wire [31:0] 		     {H} dDataRamOutLow[0:1];
   wire [31:0]		     {H} dDataRamOutHigh[0:1];
   wire [31:0]		     {H} dDataRamMuxOut;
   wire [`D_INDEX_WIDTH-1:0] dDataRamIndex;
   wire [`D_WO_WIDTH-1:0]    dDataRamOffset;
   reg [31:0] 		    {H} dDataRamIn;
   reg 			    dDataRamWe;
   wire [31:0] {H} dDataRamInv2;

   //spram #(32, (`D_INDEX_WIDTH+`D_WO_WIDTH), (2<<(`D_INDEX_WIDTH+`D_WO_WIDTH))) dc_dmem 
   ddram dc_dmem
     (
      .clk (CLK),
      //.addr ({dDataRamIndex,dDataRamOffset}),
      .index (dDataRamIndex),
      .way (dReadWay),
      .offset (dDataRamOffset),
      .din (dDataRamInv2),
      .dout0 (dDataRamOutLow[0]),
      .dout1 (dDataRamOutLow[1]),
      .dout2 (dDataRamOutHigh[0]),
      .dout3 (dDataRamOutHigh[1]),
      .we (dDataRamWe),
      .en (1'b1)

      );

   //--------------------------------------------------------------------
   // 
   // Statistics - must have NOSYNTH for synthesis
   //
   //--------------------------------------------------------------------
   
`ifdef NOSYNTH   
   // This is a good place to keep track of the cache stats
   always @(posedge CLK) begin
      // This information is for STATs only
      if (MRST) begin
	 CPU.numLoads <= `TICK 32'b0;
	 CPU.numStores <= `TICK 32'b0;
      end
      
      if (isLoad & ~pipeInhibit) begin
	 CPU.numLoads <= `TICK CPU.numLoads + 1;
      end
      if (isStore & ~pipeInhibit) begin
	 CPU.numStores <= `TICK CPU.numStores + 1;
      end
   end
`endif

   //--------------------------------------------------------------------
   //
   // Pipeline interface
   //
   //--------------------------------------------------------------------

   // These module outputs control how the rest of the CPU stalls
   //assign pcInhibit = 
   //assign pipeInhibit =

   assign pipeInhibit = dStall | iStall;

   always @(posedge CLK) begin
      if (MRST) begin
         pcInhibit <= `TICK 1'b0;
      end
      else begin
         pcInhibit <= `TICK pipeInhibit;
      end
   end
   
   // I$
   assign Iin = (!iStall) ? iDataRamMuxOut : 32'b0;

   // D$
   assign cacheOut = isLoad ? dDataRamMuxOut : 32'b0;

   //--------------------------------------------------------------------
   //
   // Instruction cache
   //
   //--------------------------------------------------------------------

   // SUH: from lab4 mem.v
   // 4-way associative cache. (0, 1) are low cache, (2, 3) are high cache.
   assign iHit0 = (iTagRamOutLow[0] == Iaddr[`I_TAG]) & (iStateRamOutLow[0][`I_VALID]);
   assign iHit1 = (iTagRamOutLow[1] == Iaddr[`I_TAG]) & (iStateRamOutLow[1][`I_VALID]);
   assign iHit2 = (iTagRamOutHigh[0] == Iaddr[`I_TAG]) & (iStateRamOutHigh[0][`I_VALID]);
   assign iHit3 = (iTagRamOutHigh[1] == Iaddr[`I_TAG]) & (iStateRamOutHigh[1][`I_VALID]);
   
   assign iHitNaive = iHit0 | iHit1 | iHit2 | iHit3;
   
   assign iHit = (ReadLabel == 0) ? ((iHit0 || iHit1) ? 1 : 0) : 
                                    ((iHit0 || iHit1 || iHit2 || iHit3)? 1 : 0);
                                       
   assign iDataRamMuxOut = (ReadLabel==0)? (iHit0 ? iDataRamOutLow[0] :        
						   (iHit1 ? iDataRamOutLow[1] : 32'b0)) :
						   (iHit0 ? iDataRamOutLow[0]:
						    iHit1 ? iDataRamOutLow[1]:
						    iHit2 ? iDataRamOutHigh[0] :
						   iHit3 ? iDataRamOutHigh[1] : 32'b0);
						   
   always @(*) begin
	  // this code maintains an invariant that Way dWay = Way iWay
	  if (ReadLabel == 1'b0) begin
	  	if (iHit0 || iHit1) begin
			iWay <= iHit0 ? 2'b00 : 2'b01;
		end
		else begin
			iWay <= I3[20]? 2'b01 : 2'b00;
		end
	  end
	  else begin
		if (iHit0 || iHit1 || iHit2 || iHit3) begin
			iWay <= iHit0 ? 2'b00 : iHit1 ? 2'b01 : iHit2 ? 2'b10 : 2'b11;
		end
		else begin
			iWay <= I3[20]? 2'b10 : 2'b11;
		end
	  end
	end
				 
   assign iStall = ~iHit | (iFsmState != IFSM_IDLE);
   
   // Memory module interfaces
   assign iTagRamIndex = Iaddr[`I_INDEX];
   assign iTagRamIn = Iaddr[`I_TAG];

   assign iStateRamIndex = Iaddr[`I_INDEX];
   assign iStateRamIn = 2'b01;

   assign iDataRamIndex = Iaddr[`I_INDEX];
   assign iDataRamOffset = (iFsmState == IFSM_IDLE) ? Iaddr[`I_WO] : iOffset;

   assign iMemAddr = Iaddr;

   // I$ FSM - this always block handles accesses to the I$
   always @(posedge CLK) begin
      if (MRST) begin
         // Initialize the state to IDLE, wait for an access
         iFsmState <= `TICK IFSM_IDLE;

         // Signals for SRAM modules
         iTagRamWe <= `TICK 1'b0;
         iStateRamWe <= `TICK 1'b0;
         iDataRamWe <= `TICK 1'b0;
         iOffset <= `TICK {(`I_WO_WIDTH){1'b0}};
         iDataRamIn <= `TICK 32'b0;

         // Signals for the memory interface 
         iMemRead <= `TICK 1'b0;

`ifdef NOSYNTH   
         // Stats
         CPU.numIMisses <= `TICK 32'b0;
`endif

      end // if (MRST) 
      else begin
         // FSM 
         case (iFsmState)  // synopsys parallel_case

            // IDLE - ready for an access from the core. handle a hit.
            IFSM_IDLE: begin
               // stay in the same state for a hit,
               // move to the miss state on a miss 
               if (!iHit) begin
                  iFsmState <= `TICK IFSM_WAITMEM;

                  // initiate the memory access
                  iMemRead <= `TICK 1'b1;

`ifdef NOSYNTH   
                  // Stats
                  CPU.numIMisses <= `TICK CPU.numIMisses + 1;
`endif
               end                
            end

            // MISS - wait for the main memory to return data
            IFSM_WAITMEM: begin
               // wait until there is a valid signal from memory
               if (iMemValid) begin
                  iFsmState <= `TICK IFSM_REFILL;

                  // start writing to data ram 
		  if (Write == 1'b0) begin // DZ: extra logic for type system
                  	iDataRamWe <= `TICK 1'b1;
                  	iDataRamIn <= `TICK Bus;
	  	  end
               end                
            end

            // REFILL - write data from memory to the cache
            IFSM_REFILL: begin
               // after the last word, go back to IDLE 
               if (iOffset == `I_MAX_OFFSET) begin
                  iFsmState <= `TICK IFSM_IDLE;

                  // Signals for SRAM modules
                  iTagRamWe <= `TICK 1'b0;
                  iStateRamWe <= `TICK 1'b0;
                  iDataRamWe <= `TICK 1'b0;
                  iOffset <= `TICK {(`I_WO_WIDTH){1'b0}};
                  iDataRamIn <= `TICK 32'b0;

                  // Signals for the memory interface 
                  iMemRead <= `TICK 1'b0;
               end                
               else begin
                  // increment the offset
                  iOffset <= `TICK iOffset + 1;

                  // write the data ram 
		  if (Write == 1'b0) begin // DZ: extra logic for type system
                  	iDataRamWe <= `TICK 1'b1;
                  	iDataRamIn <= `TICK Bus;
	  	  end

                  // Update the tag and the state in the last cycle
                  iTagRamWe <= `TICK (iOffset == (`I_MAX_OFFSET-1));
                  iStateRamWe <= `TICK (iOffset == (`I_MAX_OFFSET-1));
               end                
            end

         endcase

      end // else
   end // always @ (posedge CLK)
   

   //--------------------------------------------------------------------
   //
   // Data cache
   //
   //--------------------------------------------------------------------

   // This always block handles simple decoding of isLoad or isStore
   always @(I3) begin
      if (((I3[`op] == `LW) || (I3[`op] == `LH) || ( I3[`op] == `LHU) || (I3[`op] == `LBU) || (I3[`op] == `LB))) begin
	 isLoad = 1;
      end
      else begin
	 isLoad = 0;
      end
      
      if ((I3[`op] == `SW) || (I3[`op] == `SH) || (I3[`op] == `SB)) begin
	 isStore = 1;
      end
   else begin
      isStore = 0;
   end
      
      // Set the data size correctly
      if (I3[`op] == `SH) begin
	 Dsize = `SIZE_HALF;
      end
      else if (I3[`op] == `SB) begin
	 Dsize = `SIZE_BYTE;
      end
      else begin
	 Dsize = `SIZE_WORD;
      end
   end
   
   // Signals to handle the data size
   assign sa = (Dsize == `SIZE_BYTE) ? (( ~MAR & 32'h3) << 3) : 5'bz,
     	  sa = (Dsize == `SIZE_HALF) ? (((~MAR >> 1) & 32'h1) << 4) : 5'bz,
     	  sa = (Dsize == `SIZE_WORD) ? 0 : 5'bz;
   
   assign 
	  mask = (Dsize == `SIZE_BYTE) ? (32'hff << sa) : 32'bz,
	  mask = (Dsize == `SIZE_HALF) ? (32'hffff << sa) : 32'bz,
	  mask = (Dsize == `SIZE_WORD) ? 0 : 32'bz;

   // Address from the previous cycle
   always @(posedge CLK) begin
      if (MRST) begin
         rMAR <= `TICK 32'b0;
      end
      else begin
         rMAR <= `TICK MAR;
      end
   end

   // Main D$ control signals
   //assign dHit = 
   //assign dStall = 

   // SUH: from lab4 mem.v
   // 4-dWay associative cache. (0, 1) are low cache, (2, 3) are high cache. 
   assign dHit0 = (dTagRamOutLow[0] == MAR[`D_TAG]) & (dStateRamOutLow[0][`D_VALID]);
   assign dHit1 = (dTagRamOutLow[1] == MAR[`D_TAG]) & (dStateRamOutLow[1][`D_VALID]);
   assign dHit2 = (dTagRamOutHigh[0] == MAR[`D_TAG]) & (dStateRamOutHigh[0][`D_VALID]);
   assign dHit3 = (dTagRamOutHigh[1] == MAR[`D_TAG]) & (dStateRamOutHigh[1][`D_VALID]);
   
   assign dHitNaive = dHit0 | dHit1 | dHit2 | dHit3;  // Hit signal which doesn't consider security
   
   assign dHit = (ReadLabel == 0) ? ((dHit0 | dHit1) ? 1 : 0) :
                                    ((dHit0 | dHit1 | dHit2 | dHit3)? 1 : 0);
   
   assign dDataRamMuxOut = dHit0 ? dDataRamOutLow[0] :        //doesn't affect timing
						   (dHit1 ? dDataRamOutLow[1] :
						   (dHit2 ? dDataRamOutHigh[0] :
						   (dHit3 ? dDataRamOutHigh[1] : 32'b0)));			
				 		   
   assign dStall = ((isLoad | isStore) & (~dHit | (dFsmState != DFSM_IDLE)));
   
   // RAM module interfaces
   assign dTagRamIndex = MAR[`D_INDEX];
   assign dTagRamIn = MAR[`D_TAG];

   assign dStateRamIndex = (dFsmState == DFSM_STOREHIT) ? rMAR[`D_INDEX] : MAR[`D_INDEX];

   assign dDataRamIndex = (dFsmState == DFSM_STOREHIT) ? rMAR[`D_INDEX] : MAR[`D_INDEX];
   assign dDataRamOffset = (dFsmState == DFSM_REFILL) ? dOffset[`I_WO_WIDTH-1:0] :
                           ((dFsmState == DFSM_WRITEBACK) ? dOffset[`I_WO_WIDTH-1:0] : 
                            ((dFsmState == DFSM_STOREHIT) ? rMAR[`D_WO] : MAR[`D_WO]));

   // Memory interface 
   assign dMemBus = (dWriteWay == 2'b00) ? dDataRamOutLow[0] :        //doesn't affect timing
				   (dWriteWay == 2'b01) ? dDataRamOutLow[1] :
				   (dWriteWay == 2'b10) ? dDataRamOutHigh[0] :
				   (dWriteWay == 2'b11) ? dDataRamOutHigh[1] : 32'b0;

   assign dDataRamInv2 = ((dFsmState == DFSM_REFILL) && (dHit == 1'b0) && (ReadLabel == 1'b0) && (dHitNaive == 1)) ? dDataRamMuxOut : dDataRamIn;
   
   reg[1:0] tempdWay;
   reg[1:0] rtempdWay;
   
   always @(*) begin
   	  if (ReadLabel == 1'b0) begin
	  	if (dHit0 | dHit1) begin
			tempdWay <= dHit0 ? 2'b00 : 2'b01;
	  	end
		else begin
			tempdWay <= I3[20]? 2'b01 : 2'b00;
		end
	  end
	  else begin
	  	if (dHit0 | dHit1 |dHit2|dHit3) begin 
            tempdWay <= (dHit0? 2'b00 : dHit1? 2'b01: dHit2 ? 2'b10 : 2'b11);         // the dWay which gets cache hit
		end
		else begin
			tempdWay <= I3[20]? 2'b11 : 2'b10;
		end
	  end
   end
   
   always @(posedge CLK) begin
      if (MRST) begin
         rtempdWay <= `TICK 2'b0;
      end
      else begin
         rtempdWay <= `TICK tempdWay;
      end
   end
   
   always @(*) begin
   	  if (ReadLabel == 1'b0) begin
	  	if (dHit0 | dHit1) begin
			dWriteWay <= dHit0 ? 2'b00 : 2'b01;
	  	end
		else begin
			dWriteWay <= I3[20]? 2'b01 : 2'b00;
		end
	  end
	  else begin
	  	if (dHit2|dHit3) begin 
            dWriteWay <= (dHit2 ? 2'b10 : 2'b11);         // the dWay which gets cache hit
		end
		else begin
			dWriteWay <= I3[20]? 2'b11 : 2'b10;
		end
	  end
   end
   
   assign dReadWay = (dFsmState == DFSM_STOREHIT) ? rtempdWay : tempdWay;
   assign dStateWay = ((dFsmState == DFSM_REFILL) && ((dOffset == `D_MAX_OFFSET + 1) || (dOffset == `D_MAX_OFFSET))) ? (dHit2 ? 2'b10 : 2'b11) : dWriteWay;


   // D$ FSM - this always block handles accesses to the D$
   always @(posedge CLK) begin
      if (MRST) begin
         // Initialize the state to IDLE, wait for an access
         dFsmState <= `TICK IFSM_IDLE;

         // Signals for SRAM modules
         dTagRamWe <= `TICK 1'b0;
         dStateRamWe <= `TICK 1'b0;
         dStateRamIn <= `TICK 2'b0;
         dDataRamWe <= `TICK 1'b0;
         dOffset <= `TICK {(`I_WO_WIDTH){1'b0}};
         dDataRamIn <= `TICK 32'b0;

         // Signals for the memory interface 
         dMemRead <= `TICK 1'b0;
         dMemWrite <= `TICK 1'b0;
         dMemAddr <= `TICK 32'b0;
 
         // Bus select between I$ and D$
         BusSel <= `TICK 1'b0; 

`ifdef NOSYNTH   
         // Stats
         CPU.numDMisses <= `TICK 32'b0;
`endif
      end 
      else begin
         // FSM 
         case (dFsmState)  // synopsys parallel_case

            // IDLE - ready for an access from the core. handle a hit.
            DFSM_IDLE: begin
               // stay in the same state for a hit,
               if ((isLoad || isStore) && !dHit && iHit) begin
                  if (dReadWay == 2'b00 || dReadWay == 2'b01) begin
					  BusSel <= `TICK 1'b1;
					  if (dStateRamOutLow[dReadWay[0]][`D_VALID] && dStateRamOutLow[dReadWay[0]][`D_DIRTY]) begin
						 dFsmState <= `TICK DFSM_WRITEBACK;

						 // start the bus write in the next cycle
						 dMemWrite <= `TICK 1'b1;
						 dMemAddr <= `TICK {dTagRamOutLow[dReadWay[0]], MAR[`D_INDEX], dOffset[`I_WO_WIDTH-1:0], 2'b0};
					  end
					  else if (iHit) begin // no need to write-back & bus is free 
						 dFsmState <= `TICK DFSM_WAITMEM;

						 // initiate the memory access
						 dMemRead <= `TICK 1'b1;
						 dMemAddr <= `TICK MAR;

	`ifdef NOSYNTH   
						 // Stats
						 CPU.numDMisses <= `TICK CPU.numDMisses + 1;
	`endif
					  end       
                  end
                  else if (ReadLabel == 1) begin
                  BusSel <= `TICK 1'b1;
                  //if (dWay == 2'b10 || dWay == 2'b11) begin //Unnecessary check
					  if (dStateRamOutHigh[dReadWay[0]][`D_VALID] && dStateRamOutHigh[dReadWay[0]][`D_DIRTY]) begin
						 dFsmState <= `TICK DFSM_WRITEBACK;

						 // start the bus write in the next cycle
						 dMemWrite <= `TICK 1'b1;
						 dMemAddr <= `TICK {dTagRamOutHigh[dReadWay[0]], MAR[`D_INDEX], dOffset[`I_WO_WIDTH-1:0], 2'b0};
					  end                                  
					  else if (iHit) begin // no need to write-back & bus is free 
						 dFsmState <= `TICK DFSM_WAITMEM;

						 // initiate the memory access
						 dMemRead <= `TICK 1'b1;
						 dMemAddr <= `TICK MAR;

	`ifdef NOSYNTH   
						 // Stats
						 CPU.numDMisses <= `TICK CPU.numDMisses + 1;
	`endif
					  end 
				  //end
				  end
               end              
               // Store hit - update the data ram in the next cycle
               else if (isStore && dHit) begin
                  dFsmState <= `TICK DFSM_STOREHIT;

                  // Update the data array, considering sub-word stores h
                  dDataRamWe <= `TICK 1'b1;

                  if (Dsize == `SIZE_WORD) begin
	             dDataRamIn <= `TICK SMDR;
                  end
                  else if (Dsize == `SIZE_HALF) begin
	             dDataRamIn <= `TICK (dDataRamMuxOut & ~mask) | ((SMDR & 32'hffff) << sa) ;
                  end
                  else if (Dsize == `SIZE_BYTE) begin
	             dDataRamIn <= `TICK (dDataRamMuxOut & ~mask) | ((SMDR & 32'hff) << sa) ;
                  end      

               end
            end

            // MISS - wait for the main memory to return data
            DFSM_WAITMEM: begin
               // wait until there is a valid signal from memory
               if (dMemValid) begin
                  dFsmState <= `TICK DFSM_REFILL;

                  // start writing to data ram 
                  dDataRamWe <= `TICK 1'b1;
                  if (dHit == 1'b0 && (ReadLabel == 1'b0) && (dHitNaive == 1'b1)) begin
                  	dDataRamIn <= `TICK dDataRamMuxOut;
                  end
                  else begin
                  	dDataRamIn <= `TICK Bus;
                  end
               end                
            end

            // REFILL - write data from memory to the cache
            DFSM_REFILL: begin
               // after the last word, go back to IDLE 
               if (dOffset == (`D_MAX_OFFSET + 2)) begin
                  dFsmState <= `TICK DFSM_IDLE;

                  // Signals for SRAM modules
                  dTagRamWe <= `TICK 1'b0;
                  dStateRamWe <= `TICK 1'b0;
                  dOffset <= `TICK {(`I_WO_WIDTH+1){1'b0}};
               end
               else if (dOffset == (`D_MAX_OFFSET + 1))begin
                  // increment the offset
                  nDOffset = dOffset + 1;
                  dOffset <= `TICK nDOffset;
                  
				  dStateRamIn <= `TICK 2'b11;
				  dStateRamWe <= `TICK 1'b1;
				  dTagRamWe <= `TICK 1'b1;
               end
               else if (dOffset == `D_MAX_OFFSET)begin
                  // increment the offset
                  nDOffset = dOffset + 1;
                  dOffset <= `TICK nDOffset;
                  
                  if (dHit == 1'b0 && (ReadLabel == 1'b0) && (dHitNaive == 1)) begin			  	
				  	if (dStateWay == 2'b10 || dStateWay == 2'b11) begin
				  	dStateRamIn <= `TICK 2'b00;
				  	dStateRamWe <= `TICK 1;
				  	end
				  end
				  dDataRamWe <= `TICK 1'b0;
				  dDataRamIn <= `TICK 32'b0;
				  dMemRead <= `TICK 1'b0;
				  BusSel <= `TICK 1'b0;
               end                
               else begin
                  // increment the offset
                  nDOffset = dOffset + 1;
                  dOffset <= `TICK nDOffset;
                  //dOffset <= `TICK dOffset + 1;

                  // write the data ram 
                  dDataRamWe <= `TICK 1'b1;
                  
                  if (dHit == 1'b0 && (ReadLabel == 1'b0) && (dHitNaive == 1'b1)) begin
//                   	$display("REFILL HIT STATUS: %b%b%b%b%b", dHit0, dHit1, dHit2, dHit3, dHitNaive);
//                   	$display($time);
//                   	$display("MOVE DATA: %h from OFFSET %d", dDataRamMuxOut, dDataRamOffset);
                  	dDataRamIn <= `TICK dDataRamMuxOut;
                  end
                  else begin
                  	dDataRamIn <= `TICK Bus;
                  end
               end                
            end

            // STORE HIT - hit on a store. Update the data and state RAMs
            DFSM_STOREHIT: begin
               // After the update, go back to IDLE 
               dFsmState <= `TICK DFSM_IDLE;

               // Signals for SRAM modules
               dStateRamWe <= `TICK 1'b0;
               dDataRamWe <= `TICK 1'b0;
               dOffset <= `TICK {(`I_WO_WIDTH+1){1'b0}};
               dDataRamIn <= `TICK 32'b0;
               dStateRamIn <= `TICK 2'b00;
            end                

            // WRITE BACK - write data from cache to memory
            DFSM_WRITEBACK: begin
               // after the last word, go back to IDLE 
               if (dOffset == `D_MAX_OFFSET) begin
                  dFsmState <= `TICK DFSM_IDLE;

                  // Signals for the memory interface 
                  dMemWrite <= `TICK 1'b0;
                  BusSel <= `TICK 1'b0; 
                  dOffset <= `TICK {(`I_WO_WIDTH+1){1'b0}};
               end                
               else begin
                  // increment the offset
                  nDOffset = dOffset + 1;
                  dOffset <= `TICK nDOffset;
                  //dOffset <= `TICK dOffset + 1;

                  // write to memory
                  if (dReadWay == 2'b00 || dReadWay == 2'b01) begin
                  dMemAddr <= `TICK {dTagRamOutLow[dReadWay[0]], rMAR[`D_INDEX], nDOffset[`I_WO_WIDTH-1:0], 2'b0};
                  end
                  else begin
		  	if (ReadLabel == 1'b1) begin
                  		dMemAddr <= `TICK {dTagRamOutHigh[dReadWay[0]], rMAR[`D_INDEX], nDOffset[`I_WO_WIDTH-1:0], 2'b0};
	  		end
                  end
                  
                  // Update the tag and the state in the last cycle
                  dStateRamWe <= `TICK (dOffset == (`D_MAX_OFFSET-1));
                  dStateRamIn <= `TICK 2'b01;
               end                
            end

         endcase

      end // else
   end // always @ (posedge CLK)
   

   //--------------------------------------------------------------------
   //
   // Memory interface 
   //
   //--------------------------------------------------------------------

   // Select between I$ and D$
   assign Read = BusSel ? dMemRead : iMemRead;
   assign Write = dMemWrite;
   assign Addr = BusSel ? dMemAddr : iMemAddr;
   assign Bus = (Write==1'b1) ? dMemBus : 32'bz;

   assign iMemValid = BusSel ? 1'b0 : Valid;
   assign dMemValid = BusSel ? Valid : 1'b0;

   
//--------------------------------------------------------------------  

endmodule				
