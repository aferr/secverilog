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
//  $Id: mips.v,v 1.6 1999/10/19 03:39:05 heinrich Exp $
//
//-------------------------------------------------------------------------

`include "mips.h"
`include "cache.h"
`ifdef NOSYNTH
`define MEM_DELAY	#202

module TOP;
   
   wire [31:0] 	{L} Bus;
   reg [31:0] 	{L} BusReg;
   
   reg		{L} MRST, CLK;
   
   wire [31:0] 	{L} Addr;			// Address Bus between cpu & memory
   wire		{L} Read;			// Bus Read
   wire		{L} Write;			// Bus Write
   reg		{L} Valid;			// Valid signal for cache fill
   
   reg 		{L} startRead;
   reg [`D_WO_WIDTH-1:0] {L} currentWord;
   reg 			 {L} scheduled;
   
   // Create a 50% duty cycle clock
   initial begin
      CLK = 1;
      forever begin
	 `PHASE
	   CLK = 0;
	 `PHASE
	   CLK = 1;
      end 
   end 
   
   // This holds reset long enough to clear all the machine state
   initial begin
      MRST = 1;
      #86 MRST = 0;
   end 
   
   // This block is a good place to put $monitor or $dump statements
   initial
     begin
	$seed_mm;
	
	// I$ and D$ creation.
	// The args are:
	// associativity, linesize, number of lines
	
	$create_icache(4, 32, 256);
	$create_dcache(4, 32, 256);
	
     end
   
   // Memory system
   // The interface here is simple:
   //
   // Writes:
   //
   // At the posedge of the clock, if the Write signal is asserted,
   // store the word on the Bus to memory at the address on the Addr bus.
   //
   // Reads:
   // 
   // "Reads" are any kind of cache fill from the processor (note these
   // could be triggered by a load miss or a store miss, it doesn't matter)
   // At the posedge of the clock, if the Read signal is sensed the scheduled
   // signal is set, which indicates that a memory request will be served.
   // At the same time, the startRead signal is scheduled to be asserted
   // MEM_DELAY ticks later. When startRead is high and Read signal is still set,
   // the memory system places the word at Addr (which is still being driven
   // by the cpu) onto the Bus. For length MAX_OFFSET+1 cycles, the memory system
   // increments the local Addr by 4 and drives the next word on the Bus.
   // The Valid line is asserted as long as the memory system is producing
   // Valid data. After the last word in the cache line is driven,
   // the Valid line and scheduled signal are de-asserted. At that time
   // (when the read of all values is complete), the Read signal must also be
   // set low.
   
   always @(posedge CLK) begin
      if (MRST) begin
	 Valid       <= `TICK 1'b0;
	 currentWord <= `TICK 0;
	 startRead   <= `TICK 1'b0;
	 scheduled   <= `TICK 1'b0;
      end
      
      if (Read & !scheduled) begin
	 startRead <= `MEM_DELAY 1'b1;
	 scheduled <= `TICK 1'b1;
      end
      
      if (startRead) begin
	 if(Read) begin
            // Note that this implies a line size of 4 words.  It is also
            // what dictates that the I$ and the D$ have the same line size.
            // You can change the line size in the cache creation statements
            // above, but you must also change the following line, and 	
            // the defines in cache.h
            BusReg <= `TICK $load_mm({Addr[31:5], currentWord[2:0], 2'b0});
            Valid  <= `TICK 1;
            if (currentWord != `MAX_OFFSET) begin
	       currentWord <= `TICK currentWord + 1;
            end
            else begin
	       startRead <= `TICK 1'b0;
            end
	 end
	 else begin  
            Valid       <= `TICK 1'b0;
            scheduled   <= `TICK 1'b0;
            startRead   <= `TICK 1'b0;
            currentWord <= `TICK 0;
	 end
      end
      else begin
	 Valid <= `TICK 1'b0;
	 if(currentWord != 0) begin
            scheduled   <= `TICK 1'b0;
            currentWord <= `TICK 0;
	 end
      end
      
      // Handle writes to the memory system.  Partial word writes are now
      // handled in the cache!
      if (Write) begin
	 //$display("Time: %d",$time);
	 $store_mm(Addr,Bus);
	 
      end
   end // always @ (posedge CLK)
   // Drive Bus with BusReg unless a write is in progress
   assign Bus =(~Write) ? BusReg : 32'bz;

   //---------------------------------------------------------------------
   // This is the R3000
   cpu	CPU			// Instantiate CPU
     (
      .CLK	(CLK),
      .MRST	(MRST),
      .Bus	(Bus),
      .Addr  	(Addr),
      .Write 	(Write),
      .Read  	(Read),
      .Valid  	(Valid)
      );
   
   
   
endmodule
`endif //  `ifdef NOSYNTH


`ifndef NOSYNTH

module TOP (MRST,CLK,Bus,Addr,Write,Read,Valid);
   
   inout [31:0] 	Bus;

   
   input		MRST;

   input 		CLK;
   
   output [31:0] 	Addr;			// Address Bus between cpu & memory
   output		Read;			// Bus Read
   output		Write;			// Bus Write
   input		Valid;			// Valid signal for cache fill
   
   //---------------------------------------------------------------------
   // This is the R3000
   cpu	CPU			// Instantiate CPU
     (
      .CLK	(CLK),
      .MRST	(MRST),
      .Bus	(Bus),
      .Addr  	(Addr),
      .Write 	(Write),
      .Read  	(Read),
      .Valid  	(Valid)
      );
   
endmodule

`endif
