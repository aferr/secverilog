
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
   
module mem (CLK, I3, MRST, MAR, Valid, SMDR, Iaddr, Bus, Read, Write, Addr, cacheOut, Iin, pipeInhibit, pcInhibit);
   
   // clock and reset
   input		CLK;
   input		MRST;

   // signals from the processor pipeline
   input [31:0] 	I3;	// Stage 4 instruction
   input [31:0] 	MAR;
   input [31:0] 	SMDR;
   input [31:0] 	Iaddr;

   // signals to the processor pipeline
   output [31:0] 	cacheOut;
   wire [31:0] 		cacheOut;
   output [31:0] 	Iin;
   wire [31:0] 		Iin;
   output		pcInhibit;
   reg  		pcInhibit;
   output		pipeInhibit;
   wire 		pipeInhibit;
   
   // Memory bus interface
   input		Valid;
   inout [31:0] 	Bus;
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
   reg [`D_WO_WIDTH-1:0]	dOffset;
   reg [`D_WO_WIDTH-1:0]	nDOffset;

   // Memory bus signals
   reg 				BusSel;

   wire 			iMemValid;
   wire [31:0] 			iMemAddr;
   reg 				iMemRead;

   wire 			dMemValid;
   reg [31:0] 			dMemAddr;
   reg 				dMemRead;
   wire [31:0]			dMemBus;
   reg 				dMemWrite;

   // I$ control signals
   wire				iHit;
   wire				iStall;
   reg [31:0]			iCacheOut;

   // D$ control signals
   wire				dHit;
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
	
   wire [1:0]				 iWay;
   // Instruction cache tag RAM
   wire [`I_TAG_WIDTH-1:0]   iTagRamOut[0:3];
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
      .dout0 (iTagRamOut[0]),
      .dout1 (iTagRamOut[1]),
      .dout2 (iTagRamOut[2]),
      .dout3 (iTagRamOut[3]),
      .we (iTagRamWe),
      .en (1'b1)

      );

   // Instruction cache state RAM
   wire [1:0] 	             iStateRamOut[0:3];
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
      .dout0 (iStateRamOut[0]),
      .dout1 (iStateRamOut[1]),
      .dout2 (iStateRamOut[2]),
      .dout3 (iStateRamOut[3]),
      .we (iStateRamWe),
      .en (1'b1)

      );
   
   // Instruction cache data RAM 
   wire [31:0] 	             iDataRamOut[0:3];
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
      .dout0 (iDataRamOut[0]),
      .dout1 (iDataRamOut[1]),
      .dout2 (iDataRamOut[2]),
      .dout3 (iDataRamOut[3]),
      .we (iDataRamWe),
      .en (1'b1)

      );

   reg [1:0]				 dWay;
   // Data cache tag RAM 
   wire [`D_TAG_WIDTH-1:0]   dTagRamOut[0:3];
   wire [`D_INDEX_WIDTH-1:0] dTagRamIndex;
   wire [`D_TAG_WIDTH-1:0]   dTagRamIn;
   reg 			     dTagRamWe;
      
   //spram #(`D_TAG_WIDTH, `D_INDEX_WIDTH, (2<<`D_INDEX_WIDTH)) dc_tmem 
   dtram dc_tmem
     (
      .clk (CLK),
      //.addr (dTagRamIndex),
      .index (dTagRamIndex),
      .way (dWay),
      .din (dTagRamIn),
      .dout0 (dTagRamOut[0]),
      .dout1 (dTagRamOut[1]),
      .dout2 (dTagRamOut[2]),
      .dout3 (dTagRamOut[3]),
      .we (dTagRamWe),
      .en (1'b1)

      );

   // Data cache state RAM
   wire [1:0] 	             dStateRamOut[0:3];
   wire [`D_INDEX_WIDTH-1:0] dStateRamIndex;
   reg [1:0] 		     dStateRamIn;
   reg 			     dStateRamWe;
      
   //spram #(2, `D_INDEX_WIDTH, (2<<`D_INDEX_WIDTH)) dc_smem 
   dsram dc_smem 
     (
      .clk (CLK),
      //.addr (dStateRamIndex),
      .index (dStateRamIndex),
      .way (dWay),
      .din (dStateRamIn),
      .dout0 (dStateRamOut[0]),
      .dout1 (dStateRamOut[1]),
      .dout2 (dStateRamOut[2]),
      .dout3 (dStateRamOut[3]),
      .we (dStateRamWe),
      .en (1'b1)

      );

   // Data cache data RAM
   wire [31:0] 		     dDataRamOut[0:3];
   wire [31:0]			 dDataRamMuxOut;
   wire [`D_INDEX_WIDTH-1:0] dDataRamIndex;
   wire [`D_WO_WIDTH-1:0]    dDataRamOffset;
   reg [31:0] 		    dDataRamIn;
   reg 			    dDataRamWe;

   //spram #(32, (`D_INDEX_WIDTH+`D_WO_WIDTH), (2<<(`D_INDEX_WIDTH+`D_WO_WIDTH))) dc_dmem 
   ddram dc_dmem
     (
      .clk (CLK),
      //.addr ({dDataRamIndex,dDataRamOffset}),
      .index (dDataRamIndex),
      .way (dWay),
      .offset (dDataRamOffset),
      .din (dDataRamIn),
      .dout0 (dDataRamOut[0]),
      .dout1 (dDataRamOut[1]),
      .dout2 (dDataRamOut[2]),
      .dout3 (dDataRamOut[3]),
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

   // Main I$ control signals
   // assign iHit =
   // assign iStall =
   // assign Iin 

   // 4-way associative cache. (0, 1) are low cache, (2, 3) are high cache.
   assign iHit0 = (iTagRamOut[0] == Iaddr[`I_TAG]) & (iStateRamOut[0][`I_VALID]);
   assign iHit1 = (iTagRamOut[1] == Iaddr[`I_TAG]) & (iStateRamOut[1][`I_VALID]);
   assign iHit2 = (iTagRamOut[2] == Iaddr[`I_TAG]) & (iStateRamOut[2][`I_VALID]);
   assign iHit3 = (iTagRamOut[3] == Iaddr[`I_TAG]) & (iStateRamOut[3][`I_VALID]);
   
   assign iHit = iHit0 | iHit1 | iHit2 | iHit3;
   
   assign iDataRamMuxOut = iHit0 ? iDataRamOut[0] :        
						   iHit1 ? iDataRamOut[1] : 
						   iHit2 ? iDataRamOut[2] :
						   iHit3 ? iDataRamOut[3] : 32'b0;
						   
   assign iWay = iHit0 ? 2'b00 :        
				 iHit1 ? 2'b01 : 
				 iHit2 ? 2'b10 :
				 iHit3 ? 2'b11 : I3[21:20];
				 
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
                  iDataRamWe <= `TICK 1'b1;
                  iDataRamIn <= `TICK Bus;
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
                  iDataRamWe <= `TICK 1'b1;
                  iDataRamIn <= `TICK Bus;

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
   assign dHit0 = (dTagRamOut[0] == MAR[`D_TAG]) & (dStateRamOut[0][`D_VALID]);
   assign dHit1 = (dTagRamOut[1] == MAR[`D_TAG]) & (dStateRamOut[1][`D_VALID]);
   assign dHit2 = (dTagRamOut[2] == MAR[`D_TAG]) & (dStateRamOut[2][`D_VALID]);
   assign dHit3 = (dTagRamOut[3] == MAR[`D_TAG]) & (dStateRamOut[3][`D_VALID]);
   
   assign dHit = dHit0 | dHit1 | dHit2 | dHit3;
   
   assign dDataRamMuxOut = dHit0 ? dDataRamOut[0] :        //doesn't affect timing
						   (dHit1 ? dDataRamOut[1] :
						   (dHit2 ? dDataRamOut[2] :
						   (dHit3 ? dDataRamOut[3] : 32'b0)));			
				 		   
   assign dStall = ((isLoad | isStore) & (~dHit | (dFsmState != DFSM_IDLE)));
   
   // RAM module interfaces
   assign dTagRamIndex = MAR[`D_INDEX];
   assign dTagRamIn = MAR[`D_TAG];

   assign dStateRamIndex = (dFsmState == DFSM_STOREHIT) ? rMAR[`D_INDEX] : MAR[`D_INDEX];

   assign dDataRamIndex = (dFsmState == DFSM_STOREHIT) ? rMAR[`D_INDEX] : MAR[`D_INDEX];
   assign dDataRamOffset = (dFsmState == DFSM_REFILL) ? dOffset :
                           ((dFsmState == DFSM_WRITEBACK) ? dOffset : 
                            ((dFsmState == DFSM_STOREHIT) ? rMAR[`D_WO] : MAR[`D_WO]));

   // Memory interface 
   assign dMemBus = dDataRamOut[dWay];

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
//          $display("time = %d", $time);
//          $disasm (I3);
//          $display("MAR = %h", MAR);
//          $display("iFsmState = %d", iFsmState);
//          $display("dFsmState = %d", dFsmState);
//          $display("dWay = %d", dWay);
//          $display("dStall = %b", dStall);
//          $display("iStall = %b", iStall);
//          $display("pipeInhibit = %b\n", pipeInhibit);
         case (dFsmState)  // synopsys parallel_case

            // IDLE - ready for an access from the core. handle a hit.
            DFSM_IDLE: begin
               // stay in the same state for a hit,
               // move to the miss state on a miss 
               if ((isLoad || isStore) && !dHit && iHit) begin
                  // need to write-back first & bus is free
                  if (dStateRamOut[I3[21:20]][`D_VALID] && dStateRamOut[I3[21:20]][`D_DIRTY]) begin
                     dFsmState <= `TICK DFSM_WRITEBACK;

                     // start the bus write in the next cycle
                     dMemWrite <= `TICK 1'b1;
                     dMemAddr <= `TICK {dTagRamOut[I3[21:20]], MAR[`D_INDEX], dOffset, 2'b0};
                     BusSel <= `TICK 1'b1; 
                  end                
                  else if (iHit) begin // no need to write-back & bus is free 
                     dFsmState <= `TICK DFSM_WAITMEM;

                     // initiate the memory access
                     dMemRead <= `TICK 1'b1;
                     dMemAddr <= `TICK MAR;
                     BusSel <= `TICK 1'b1; 

`ifdef NOSYNTH   
                     // Stats
                     CPU.numDMisses <= `TICK CPU.numDMisses + 1;
`endif
                  end 
                  dWay <= `TICK I3[21:20];               
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

                  // update the dirty bit
                  dStateRamWe <= `TICK 1'b1;
                  dStateRamIn <= `TICK 2'b11;
//                   $display("STORE HIT STATUS: %b%b%b%b", dHit0, dHit1, dHit2, dHit3);
//                    $display("STORE DATA: %h", dDataRamIn);
                  // update the dWay
                  dWay <= `TICK dHit0 ? 2'b00 :        
                  				dHit1 ? 2'b01 : 
                 				dHit2 ? 2'b10 :
                 				dHit3 ? 2'b11 : 2'b00;
               end
            end

            // MISS - wait for the main memory to return data
            DFSM_WAITMEM: begin
               // wait until there is a valid signal from memory
               if (dMemValid) begin
                  dFsmState <= `TICK DFSM_REFILL;

                  // start writing to data ram 
                  dDataRamWe <= `TICK 1'b1;
                  dDataRamIn <= `TICK Bus;
               end                
            end

            // REFILL - write data from memory to the cache
            DFSM_REFILL: begin
               // after the last word, go back to IDLE 
               if (dOffset == `D_MAX_OFFSET) begin
                  dFsmState <= `TICK DFSM_IDLE;

                  // Signals for SRAM modules
                  dTagRamWe <= `TICK 1'b0;
                  dStateRamWe <= `TICK 1'b0;
                  dDataRamWe <= `TICK 1'b0;
                  dOffset <= `TICK {(`I_WO_WIDTH){1'b0}};
                  dDataRamIn <= `TICK 32'b0;

                  // Signals for the memory interface 
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
                  dDataRamIn <= `TICK Bus;

                  // Update the tag and the state in the last cycle
                  dTagRamWe <= `TICK (dOffset == (`D_MAX_OFFSET-1));
                  dStateRamWe <= `TICK (dOffset == (`D_MAX_OFFSET-1));
                  dStateRamIn <= `TICK 2'b01;
//                   $display("REFILL HIT STATUS: %b%b%b%b", dHit0, dHit1, dHit2, dHit3);
//                   	$display($time);
//                   	$display("MOVE DATA: %h from OFFSET %d", Bus, dDataRamOffset);
               end                
            end

            // STORE HIT - hit on a store. Update the data and state RAMs
            DFSM_STOREHIT: begin
               // After the update, go back to IDLE 
               dFsmState <= `TICK DFSM_IDLE;

               // Signals for SRAM modules
               dStateRamWe <= `TICK 1'b0;
               dDataRamWe <= `TICK 1'b0;
               dOffset <= `TICK {(`I_WO_WIDTH){1'b0}};
               dDataRamIn <= `TICK 32'b0;
            end                

            // WRITE BACK - write data from cache to memory
            DFSM_WRITEBACK: begin
               // after the last word, go back to IDLE 
               if (dOffset == `D_MAX_OFFSET) begin
                  dFsmState <= `TICK DFSM_IDLE;

                  // Signals for the memory interface 
                  dMemWrite <= `TICK 1'b0;
                  BusSel <= `TICK 1'b0; 
                  dOffset <= `TICK {(`I_WO_WIDTH){1'b0}};
               end                
               else begin
                  // increment the offset
                  nDOffset = dOffset + 1;
                  dOffset <= `TICK nDOffset;
                  //dOffset <= `TICK dOffset + 1;

                  // write to memory
                  dMemWrite <= `TICK 1'b1;
                  dMemAddr <= `TICK {dTagRamOut[dWay], MAR[`D_INDEX], nDOffset, 2'b0};

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
   assign Bus = (Write) ? dMemBus : 32'bz;

   assign iMemValid = BusSel ? 1'b0 : Valid;
   assign dMemValid = BusSel ? Valid : 1'b0;

   
//--------------------------------------------------------------------  

endmodule			
