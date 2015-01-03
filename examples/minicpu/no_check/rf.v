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
//  $Id: rf.v,v 1.3 2000/10/14 19:21:41 heinrich Exp $
//
//-------------------------------------------------------------------------

`include "mips.h"
   
module	rf(WCLK, RSaddr, RTaddr, RDaddr, RS, RT, RD);

input		WCLK;	// Write clock for RD write port

input	[4:0]	RSaddr;	// Read address for source read port
input	[4:0]	RTaddr;	// Read address for target read port
input	[4:0]	RDaddr;	// Store address for destination write port
input	[31:0]	RD;	// Destination write port

output	[31:0]	RS;	// Source read port
reg	[31:0]	RS;	// Source read port
output	[31:0]	RT;	// Target read port
reg	[31:0]	RT;	// Target read port

// A 32 x 32 bit memory array
reg	[31:0]	RAM [0:31];

// ------------------------------------------------------------
// This is the register file!
//
// It is initially set to 0.  It is written at posedge WCLK.
// Reads are done combinationally based on the RSaddr and RTaddr
// register specifiers. Register reads are done in the Decode stage
// and set the RS and RT busses appropriately
// ------------------------------------------------------------

initial
begin
   // Initialize registers with zeros
   RAM[0] = 32'b0;
end

//`include "sync.h"
//--------------------------------------------------------------------

always @(posedge WCLK) begin
   // Register r0 is read-only
   if (RDaddr != 5'b0) begin
      // Write RD data to cell addressed by RDaddr
      //$display("Writing register %h with data %h", RDaddr, RD);
      RAM[RDaddr] <= `TICK RD;
   end
end
   
always @(RAM[RSaddr]) begin
   // Fetch RS data using RSaddr
   RS = RAM[RSaddr];
end

always @(RAM[RTaddr]) begin
   // Fetch RT data using RTaddr
   RT = RAM[RTaddr];
end

//--------------------------------------------------------------------

endmodule

